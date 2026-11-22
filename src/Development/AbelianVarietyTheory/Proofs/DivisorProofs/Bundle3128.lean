import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1397
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1941
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1444
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1447
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1782
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3073
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2058
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1942
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1907
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsThetaFunctionStandardPairSecond
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1883
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1724
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualSkewIdealLatticeIsSelfDual
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLine
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumUnderAdelicPairModulusOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0260
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslateGaloisRationalityCmPoints
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0299
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteThetaPairTestVectorExpansion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0420
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0064
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2282
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3068
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0045
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsMultiplicativeGroup
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0012
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2274
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2291
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2367
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3087
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2280
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0067
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0089
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3078
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0032
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3079
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0031
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3080
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0046
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeStabilizerVacuumEigenvalueEqOneInertPlace
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

namespace GlobalTheory.DblVac

theorem eigen_eq_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ k ∈ GlobalTheory.InertSph.KAt σ G.W v, ∀ c : ℂ, Acts (evFin F v) (om (1, k)) (G.M.vac v) (c • G.M.vac v) → c = 1 := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hT v w hw hv k hk c hc
  obtain ⟨dd, omd, hdc, hsp, hbox⟩ := hT.weil.1.2
  have hvac := hT.geo.hM.vac v
  obtain ⟨r, hr, hr0⟩ := GlobalTheory.T.exists_complementaryAdelicSchwartz_tensor_ne_zero _ v (G.M.vac v) hvac.1 hvac.2.1
  set V₀ := tens (evFin F v) (G.M.vac v) r with hV₀
  set S := boxFun V₀ (fun x => star (V₀ x)) with hS
  have hS0 : ∃ x, S x ≠ 0 := by
    obtain ⟨x, hx⟩ := Function.ne_iff.mp hr0
    refine ⟨Sum.elim x x, ?_⟩
    simp only [hS, boxFun, Sum.elim_comp_inl, Sum.elim_comp_inr, Pi.zero_apply] at hx ⊢
    exact mul_ne_zero hx (star_ne_zero.mpr hx)
  let H : Subgroup (GlobalTheory.DblVac.UD σ G.W) :=
    { carrier := {g | omd g S = S}
      one_mem' := by simp
      mul_mem' := fun {x y} hx hy => by
        simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
        rw [hy, hx]
      inv_mem' := fun {x} hx => by
        simp only [Set.mem_setOf_eq] at *
        conv_lhs => rw [← hx]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hD : ∀ p ∈ GlobalTheory.DblVac.KD σ G.W v, p ∈ GlobalTheory.DblVac.PDiag σ G.W → p ∈ H := fun p hp hpd => by
    obtain ⟨μ, hμ⟩ := GlobalTheory.T.inertPlace_latticeStabilizer_scales_doubledVacuum F E σ B a a' G X om om' hT v w hw hv dd omd hdc hsp r hr p hp
    have h1 := GlobalTheory.T.diagonalStabilizer_doubledVacuum_eigenvalue_eq_one F E σ B a a' G X om om' hT v w hw hv dd omd hdc hsp r hr hr0 p hp hpd μ hμ
    show omd p S = S
    rw [hμ, h1, one_smul]
  have hA : ∀ q ∈ GlobalTheory.DblVac.KD σ G.W v, q ∈ GlobalTheory.DblVac.PAnti σ G.W → q ∈ H := fun q hq hqa => by
    obtain ⟨w₀, hw₀, hW⟩ := GlobalTheory.T.exists_diagOneNegOne_conj_antidiagonalStabilizer_mem σ G.W v
    obtain ⟨h1, h2⟩ := hW q hq hqa
    have hq' : omd (w₀ * q * w₀⁻¹) S = S := hD _ h1 h2
    obtain ⟨μ, hμ⟩ := GlobalTheory.T.inertPlace_latticeStabilizer_scales_doubledVacuum F E σ B a a' G X om om' hT v w hw hv dd omd hdc hsp r hr w₀ hw₀
    have hinv : μ • omd w₀⁻¹ S = S := by
      rw [← LinearMap.map_smul, ← hμ, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        Module.End.one_apply]
    have e : q = w₀⁻¹ * (w₀ * q * w₀⁻¹) * w₀ := by group
    show omd q S = S
    rw [e, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hμ, LinearMap.map_smul, hq',
      LinearMap.map_smul, hinv]
  obtain ⟨gd, hgd, hgdK⟩ := GlobalTheory.T.exists_diag_mem_doubledVacuumLatticeStabilizer σ G.W v k hk
  have hfix : omd gd S = S := GlobalTheory.T.inertPlace_lattice_stabiliser_generated_diag_antidiag F E σ B a a' G X om om' hT v w hw H hD hA gd hgdK
  have hb := hbox k gd hgd V₀ hr.2 (fun x => star (V₀ x)) (GlobalTheory.T.conj_mem_adelicSchwartzSpaceNumberField_of_mem _ V₀ hr.2)
  have hk1 : (om.comp (MonoidHom.inr _ _)) k V₀ = c • V₀ := by
    rw [MonoidHom.comp_apply, MonoidHom.inr_apply, hV₀, hc r hr]
    funext x
    simp [tens, mul_assoc]
  rw [hk1] at hb
  have hcS : c • S = S := by
    calc c • S = boxFun (c • V₀) (fun x => star (V₀ x)) := by
          funext x
          simp [hS, boxFun, mul_assoc]
      _ = omd gd S := hb.symm
      _ = S := hfix
  obtain ⟨x, hx⟩ := hS0
  have := congrFun hcS x
  simp only [Pi.smul_apply, smul_eq_mul] at this
  exact mul_right_cancel₀ hx (this.trans (one_mul _).symm)

end GlobalTheory.DblVac
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelIndicatorReadsNormPowerUnitVector
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotSmallDict GlobalTheory.NormExact
open scoped Pointwise

noncomputable section

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

namespace GlobalTheory.SkewLevel

theorem sum_section {M Q : Type} [AddCommGroup M] [AddCommGroup Q] [Fintype Q] (π : M →+ Q) (Z : Q → M) (hZ : ∀ q, π (Z q) = q)
    (χ : M → ℂ) (hadd : ∀ x y, χ (x + y) = χ x * χ y) (hker : ∀ x, π x = 0 → χ x = 1) {m : M} (hm : χ m ≠ 1) :
    ∑ q, χ (Z q) = 0 := by
  have h1 : ∀ q, χ (Z (q + π m)) = χ m * χ (Z q) := fun q => by
    have e : Z (q + π m) = (Z (q + π m) - (m + Z q)) + (m + Z q) := by abel
    rw [e, hadd, hker _ (by rw [map_sub, map_add, hZ, hZ]; abel), one_mul, hadd]
  have h2 : ∑ q, χ (Z q) = χ m * ∑ q, χ (Z q) := by
    rw [Finset.mul_sum, ← Equiv.sum_comp (Equiv.addRight (π m)) (fun q => χ (Z q))]
    exact Finset.sum_congr rfl fun q _ => h1 q
  have h3 : (χ m - 1) * ∑ q, χ (Z q) = 0 := by linear_combination -h2
  exact (mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 hm)

variable {D : D7}

theorem pt_mem_iff {δ : ℂ} {a d : ℕ} (L : Submodule (𝓞 D.host.E) (Fin a → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin d → D.host.E)) (y : VC D a d) :
    y ∈ La D (tor0 D ⊤ δ) L L' ↔ ∃ z ∈ YYl D L L', GlobalTheory.ThetaLatticePoints.ptHom D ⊤ δ a d z = y := by
  constructor
  · intro hy
    have h : La D (tor0 D ⊤ δ) L L' ≤ (YYl D L L').toAddSubgroup.map (GlobalTheory.ThetaLatticePoints.ptHom D ⊤ δ a d) := by
      refine (AddSubgroup.closure_le _).2 ?_
      rintro _ ⟨w, hw, A, hA, rfl⟩
      obtain ⟨c, -, rfl⟩ := (GlobalTheory.CurveLattice.mem_lamOf D ⊤ δ w).1 hw
      exact ⟨((c : D.host.K) : D.host.E) • A, (YYl D L L').smul_mem (algebraMap (𝓞 D.host.K) (𝓞 D.host.E) c) hA,
        GlobalTheory.ThetaLatticePoints.ptHom_smul D ⊤ δ a d c A⟩
    exact h hy
  · rintro ⟨z, hz, rfl⟩
    exact AddSubgroup.subset_closure ⟨δ, AddSubgroup.subset_closure ⟨1, trivial, by simp⟩, z, hz, rfl⟩

theorem reads_sum {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {a d : ℕ} {hS : S.rank = a} {hT : T.rank = d}
    {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {r : D.host.E} {ι : Type} (s : Finset ι) (G : ι → VC D a d → ℂ) (f : ι → WO S T → ℂ)
    (h : ∀ i, Reads ψ θ hS hT cc δ r (G i) (f i)) : Reads ψ θ hS hT cc δ r (∑ i ∈ s, G i) (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨(GlobalTheory.FinWeilO.thetaSub ψ S T).zero_mem, fun w _ => by simp⟩
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    exact (h i).add ih

theorem reads_level : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) {a d : ℕ} (hS : S.rank = a) (hT : T.rank = d) (δ : ℂ),
    D.host.ccK = ⊤ → Setup ψ θ S T ⊤ δ 1 →
    ∀ (LS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    IsStdLat LS → IsStdLat LT → IsSelfDualC S LS → IsSelfDualC T LT →
    ∀ (e : Formalism.L2.Theta.AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (c : Formalism.L2.DIV.Pl D.host.E → ℕ), GoodIdem e P →
    IsSBHalf (cA D e) (latO S T LS LT fun _ => True) (cosetFn (cA D e) (D.host.conj • modul P c) (0 : WO S T)) →
    ∀ (κ : ℂ) (e0 : VC D a d → ℂ) (vac : WO S T → ℂ), e0 ∈ Th D (tor0 D ⊤ δ) (stdL D a) (stdL D d) →
    Reads ψ θ hS hT ⊤ δ 1 (κ • e0) vac → IsLatVac (heisO ψ S T) (latO S T LS LT fun _ => True) vac →
    ∀ Tm : (WO S T → ℂ) →ₗ[ℂ] (WO S T → ℂ),
    IsPlaceModel ψ (symplO S T) (heisO ψ S T) (cA D e) (latO S T LS LT fun _ => True) 1 vac Tm →
    ∃ ζ : ℂ, IsRootOne ζ ∧ Reads ψ θ hS hT ⊤ δ 1
      ((κ * ζ) • ((Real.sqrt ((Ideal.absNorm (D.host.conj • modul P c) : ℝ) ^ (a * d)) : ℂ))⁻¹ •
        Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D (D.host.conj • modul P c) d)) e0)
      (Tm (cosetFn (cA D e) (D.host.conj • modul P c) 0)) := by
  intro D ψ θ S T a d hS hT δ hcc hset LS LT hLS hLT hSd hTd e P c he _ κ e0 vac he0 hread hvac Tm hTm
  subst hS hT
  have hc := hset.crv
  have hψ := hset.std
  have gS := hset.gS
  have hG := (GlobalTheory.InducedType.induced_type D).1
  have hne := conj_ne_bot P c
  have hidx := GlobalTheory.SkewIndex.index_inter_skew D δ hc _ hne
    (by rw [conj_conj_smul]; exact isCoprime_conj he.1 c) S.rank T.rank
  have hN0 : 0 < Ideal.absNorm (D.host.conj • modul P c) := Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 hne)
  have kp : KLat D (tor0 D ⊤ δ) (La D (tor0 D ⊤ δ) (stdL D S.rank) (skewLat D (D.host.conj • modul P c) T.rank)) :=
    Or.inr ⟨_, _, GlobalTheory.NormSum.VacMove.sd_of_moves (GlobalTheory.NormSum.VacMove.moves_one D S.rank),
      GlobalTheory.SkewLatSD.skewLat_sd D _ T.rank hne, rfl⟩
  obtain ⟨-, -, hIm, -, -, -, hq⟩ := GlobalTheory.ThetaLine.theta_line D hG ⊤ δ hc S.rank T.rank _ kp
  have hrep := GlobalTheory.ThetaConj.repInd_of_thSp D _ _ _ (La0 D (tor0 D ⊤ δ) S.rank T.rank) _ e0 hq
    (fun x hx y hy => hIm _ (GlobalTheory.GalTheta.weilElement_smul_mem_thetaLattice D hG ⊤ δ _ _ x hx) y hy) he0
  have hmem0 := pt_mem_iff (δ := δ) (stdL D S.rank) (stdL D T.rank)
  have hmem2 := pt_mem_iff (δ := δ) (stdL D S.rank) (skewLat D (D.host.conj • modul P c) T.rank)
  have hinj := GlobalTheory.ThetaLatticePoints.ptHom_injective D ⊤ (delta_ne_zero hc) S.rank T.rank
  have hkI := fun t ht htΛ hk => inId_of_kill hψ hcc gS hLS hLT hSd hTd he c (t := t) ht htΛ hk
  have hsm := fun z hz => smul_finRat_mem hψ hcc gS hLS hLT hSd hTd P c (z := z) hz
  have hhalf := fun z hz => heisO_eq_half hψ hcc gS hLS hLT hSd hTd he.1 c hvac (z := z) hz
  have hsk := fun z hz m hm => smul_skew_mem (conj_conj_ne_bot P c) (a := S.rank) (d := T.rank) (z := z) hz (m := m) hm
  rw [conj_conj_smul] at hsk
  set I := D.host.conj • modul P c with hI
  set p := GlobalTheory.ThetaLatticePoints.ptHom D ⊤ δ S.rank T.rank with hp
  set Y := YYl D (stdL D S.rank) (skewLat D I T.rank) with hY
  set A₁ := La0 D (tor0 D ⊤ δ) S.rank T.rank with hA₁
  set A₂ := La D (tor0 D ⊤ δ) (stdL D S.rank) (skewLat D I T.rank) with hA₂
  haveI : Finite (A₂ ⧸ A₁.addSubgroupOf A₂) := AddSubgroup.index_ne_zero_iff_finite.1 (by rw [hidx]; positivity)
  letI : Fintype (A₂ ⧸ A₁.addSubgroupOf A₂) := Fintype.ofFinite _
  have hcard : Fintype.card (A₂ ⧸ A₁.addSubgroupOf A₂) = Ideal.absNorm I ^ (S.rank * T.rank) := by
    rw [← hidx, AddSubgroup.index_eq_card, Nat.card_eq_fintype_card]
  obtain ⟨m, hm, u, hmu⟩ := exists_add_two he c
  have hz : ∀ q : A₂ ⧸ A₁.addSubgroupOf A₂, ∃ z ∈ Y, ((Quotient.out q : A₂) : VC D S.rank T.rank) - p (2 • z) ∈ A₁ := fun q => by
    obtain ⟨z, hz, ez⟩ := (hmem2 _).1 (Quotient.out q).2
    refine ⟨u • z, Y.smul_mem u hz, (hmem0 _).2 ⟨m • z, hsk z hz m hm, ?_⟩⟩
    rw [← ez, ← map_sub, two_nsmul, ← add_smul, ← mul_two, eq_sub_of_add_eq hmu, sub_smul, one_smul]
  choose z hzY hzq using hz
  have hp2 : ∀ w ∈ Y, p w ∈ A₂ := fun w hw => (hmem2 _).2 ⟨w, hw, rfl⟩
  let π : Y →+ A₂ ⧸ A₁.addSubgroupOf A₂ := (QuotientAddGroup.mk' _).comp
    ((p.comp Y.toAddSubgroup.subtype).codRestrict A₂ fun w => hp2 w w.2)
  have hπ : ∀ q, π ⟨2 • z q, nsmul_mem (hzY q) 2⟩ = q := fun q => by
    conv_rhs => rw [← QuotientAddGroup.out_eq' q]
    refine QuotientAddGroup.eq.2 ?_
    rw [AddSubgroup.mem_addSubgroupOf, neg_add_eq_sub]
    exact hzq q
  have hπ0 : ∀ w : Y, π w = 0 → GlobalTheory.VacUnique.finRat S T (-w.1) ∈ latO S T LS LT (fun _ => True) := fun w hw => by
    obtain ⟨w', hw', ew⟩ := (hmem0 (p w.1)).1
      ((QuotientAddGroup.eq_zero_iff (N := A₁.addSubgroupOf A₂) (⟨p w.1, hp2 w w.2⟩ : A₂)).1 hw)
    rw [finRat_mem_iff hψ hcc gS hLS hLT hSd hTd, ← hinj ew]
    exact neg_mem hw'
  have hn : ((Ideal.absNorm I ^ (S.rank * T.rank) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by positivity)
  have hfun : cosetFn (cA D e) I (0 : WO S T) = ∑ q, ((Ideal.absNorm I ^ (S.rank * T.rank) : ℕ) : ℂ)⁻¹ • fun t =>
      ψ (symplO S T t (e • GlobalTheory.VacUnique.finRat S T (2 • -z q))) * halfInd (cA D e) (latO S T LS LT fun _ => True) t := by
    funext t
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← Finset.mul_sum, ← Finset.sum_mul]
    simp only [cosetFn, halfInd, Matrix.zero_apply, sub_zero]
    by_cases h1 : t ∈ latO S T LS LT (fun _ => True) ∧ IsHalf (cA D e) t
    · have e1 : ∀ y, symplO S T t (e • y) = symplO S T t y := fun y => by
        rw [← cA_cA e, ← GlobalTheory.PlaceModel.symplO_smul, (GlobalTheory.PlaceModel.mem_half S T).1 ((GlobalTheory.PlaceModel.isHalf_iff S T).1 h1.2)]
      simp only [e1]
      rw [if_pos h1, mul_one]
      by_cases h2 : ∀ i j, GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId I (toEAf D (t i j))
      · rw [if_pos ⟨h1.2, h2⟩, Finset.sum_congr rfl fun q _ =>
          kill_of_inId hψ hcc hLS hLT hSd hTd he h1.2 h2 (hsm _ (nsmul_mem (neg_mem (hzY q)) 2)),
          Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul, mul_one, inv_mul_cancel₀ hn]
      · rw [if_neg fun h => h2 h.2]
        obtain ⟨w, hw, hw1⟩ : ∃ w ∈ Y, ψ (symplO S T t (GlobalTheory.VacUnique.finRat S T w)) ≠ 1 := by
          by_contra h
          push_neg at h
          exact h2 (hkI t h1.2 h1.1 h)
        have h3 := sum_section π (fun q => ⟨2 • z q, nsmul_mem (hzY q) 2⟩) hπ
          (fun w => ψ (symplO S T t (GlobalTheory.VacUnique.finRat S T (-w.1))))
          (fun x y => by
            rw [Submodule.coe_add, neg_add, map_add, GlobalTheory.PlaceModel.symplO_add_right, AddChar.map_add_eq_mul])
          (fun x hx => GlobalTheory.LatVac.char_sympl_eq_one hψ hSd hTd h1.1 (hπ0 x hx)) (m := ⟨-w, neg_mem hw⟩)
          (by simpa only [neg_neg] using hw1)
        simp only [smul_neg]
        rw [h3, mul_zero]
    · rw [if_neg h1, mul_zero, mul_zero, if_neg fun h => h1 ⟨(half_mem_iff hcc hLS hLT hSd hTd he t h.1).2 fun i j => (h.2 i j).1, h.1⟩]
  have hv : Tm (halfInd (cA D e) (latO S T LS LT fun _ => True)) = vac := by simpa using hTm.vac
  have hee := GlobalTheory.PlaceVec.idemSum_mul_self he.1
  have hTmΦ : Tm (cosetFn (cA D e) I 0) = ((Ideal.absNorm I ^ (S.rank * T.rank) : ℕ) : ℂ)⁻¹ •
      ∑ q, heisO ψ S T (finPt rfl rfl 1 (2 • z q)) vac := by
    rw [hfun, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    have e1 : finPt (rfl : S.rank = S.rank) (rfl : T.rank = T.rank) 1 (2 • z q) = GlobalTheory.VacUnique.finRat S T (2 • -z q) := by
      unfold finPt
      congr 1
      refine Matrix.ext fun i j => ?_
      simp
    rw [map_smul, hTm.modul _ (GlobalTheory.isSBHalf_halfInd _ _) _ (fun i j => by
      change cA D (cA D e) * (e * _) = e * _
      rw [cA_cA, ← mul_assoc, hee]), hv, hhalf _ (neg_mem (hzY q)), e1]
  have hR := (reads_sum Finset.univ _ _ fun q =>
    heisO_finPt_reads ψ θ S T rfl rfl ⊤ δ 1 hset _ _ hread (2 • z q)).smul ((Ideal.absNorm I ^ (S.rank * T.rank) : ℕ) : ℂ)⁻¹
  refine ⟨1, IsRootOne.one, ?_⟩
  rw [hTmΦ]
  convert hR using 1
  have hU : ∀ q : A₂ ⧸ A₁.addSubgroupOf A₂, ∀ y, al D (tor0 D ⊤ δ) ((Quotient.out q : A₂) : VC D S.rank T.rank) *
      U D (tor0 D ⊤ δ) ((Quotient.out q : A₂) : VC D S.rank T.rank) e0 y =
        U D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ (2 • z q)) e0 y := fun q y => by
    have h1 := congrFun (hrep _ (Quotient.out q).2 _ (hp2 _ (nsmul_mem (hzY q) 2)) (hzq q)) y
    obtain ⟨k, hk⟩ := hq _ (hp2 _ (hzY q))
    have h2 : al D (tor0 D ⊤ δ) (p (2 • z q)) = 1 := by
      rw [GlobalTheory.ThetaConj.al_of_qH D _ _ (2 * (2 * k)) (by
        rw [map_nsmul, GlobalTheory.NormSum.Expand.qH_nsmul, hk]; push_cast; ring), zpow_mul]
      norm_num
    simp only [GlobalTheory.ThetaConj.aU, h2, one_mul] at h1
    exact h1
  have hs : ((Real.sqrt ((Ideal.absNorm I : ℝ) ^ (S.rank * T.rank)) : ℂ))⁻¹ *
      ((Real.sqrt (((Ideal.absNorm I ^ (S.rank * T.rank) : ℕ) : ℝ)) : ℂ))⁻¹ =
        ((Ideal.absNorm I ^ (S.rank * T.rank) : ℕ) : ℂ)⁻¹ := by
    have h1 : (((Ideal.absNorm I ^ (S.rank * T.rank) : ℕ) : ℝ)) = (Ideal.absNorm I : ℝ) ^ (S.rank * T.rank) := by
      push_cast; rfl
    rw [h1, ← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    push_cast; rfl
  funext y
  simp only [Pi.smul_apply, smul_eq_mul, Iop, finsum_eq_sum_of_fintype, hidx, hU, Finset.sum_apply]
  rw [← hs]
  simp only [U, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun q _ => by ring

end GlobalTheory.SkewLevel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieModelIsBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DiagSqAxes

theorem lift_mul_lift₂ {S : Scheme.{0}} {A B T : Over S} [GrpObj A] [GrpObj B] (x x' : T ⟶ A) (y y' : T ⟶ B) :
    lift x y * lift x' y' = lift (x * x') (y * y') := by
  apply CartesianMonoidalCategory.hom_ext <;> simp [MonObj.mul_comp]

theorem weilIs_one_of_gen {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] (hA : IsAbelianScheme A)
    {L : LB A.left} (hL : L.IsLB) (t : L.Gen) (ht : t.IsGen) {N : ℕ} {T : Over S} {x y : T ⟶ A}
    (hx : x ^ N = 1) (hy : y ^ N = 1) : Out.WeilIs A L N x y 1 := by
  have hG := GlobalTheory.globalFns_holds
  have hM : (GlobalTheory.UU.trivRig A).L.IsLB := Out.Inh.trivLB_isLB _
  have h1 : Out.WeilIs A (GlobalTheory.UU.trivRig A).L N (x ≫ 𝟙 A) (y ≫ 𝟙 A) 1 := by
    rw [Category.comp_id, Category.comp_id]
    exact (GlobalTheory.UU.cubWeil_iff_weilIs (c := GlobalTheory.UU.trivCub A) hG hA hx hy 1).1 (GlobalTheory.UU.cubWeil_triv hx hy)
  have hw : LBIso (lbPow L 1) ((GlobalTheory.UU.trivRig A).L.pull (Over.Hom.left (𝟙 A))) :=
    LBIso.trans (GlobalTheory.isLB_lbPow hL 1) hL (pull_isLB hM _) (GlobalTheory.lbIso_lbPow_one hL)
      (GlobalTheory.ZH.AbelianFibre.lbIso_of_gens t ht (GlobalTheory.UU.unitGen _ _) (GlobalTheory.UU.unitGen_isGen _ _))
  have h2 := GlobalTheory.WeilIsogeny.weilIs_pull_hom hG hA hL hM (𝟙 A) hw h1
  simp only [Nat.cast_one, _root_.mul_one] at h2
  exact h2

theorem weilIs_axis {S : Scheme.{0}} {A B : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
    (hA : IsAbelianScheme A) (hB : IsAbelianScheme B) {P : LB B.left} (hP : P.IsLB) (ψ : A ⟶ B) [IsMonHom ψ]
    (ht : ∃ t : (P.pull ψ.left).Gen, t.IsGen) (κ : Type) [Field κ] [IsAlgClosed κ] (y : Sp κ ⟶ S) (N : ℕ)
    (hN : 0 < N) (hNk : (N : κ) ≠ 0) (a b : Over.mk y ⟶ A) (ha : a ^ N = 1) (hb : b ^ N = 1) :
    Out.WeilIs B P N (a ≫ ψ) (b ≫ ψ) 1 := by
  have hG := GlobalTheory.globalFns_holds
  obtain ⟨t, ht⟩ := ht
  have hL : (P.pull ψ.left).IsLB := pull_isLB hP _
  have pa : (a ≫ ψ) ^ N = 1 := by rw [← MonObj.pow_comp, ha, MonObj.one_comp]
  have pb : (b ≫ ψ) ^ N = 1 := by rw [← MonObj.pow_comp, hb, MonObj.one_comp]
  obtain ⟨c', hc'⟩ := GlobalTheory.WeilGeomPt.exists_weilIs_geomPt S B P hB hP κ y N hN hNk _ _ pa pb
  have h1 := GlobalTheory.WeilIsogeny.weilIs_pull_hom hG hA hL hP ψ (GlobalTheory.lbIso_lbPow_one hL) hc'
  simp only [Nat.cast_one, _root_.mul_one] at h1
  have h2 := weilIs_one_of_gen hA hL t ht ha hb
  rwa [GlobalTheory.CommutatorPairing.weilIs_unique hG hA hL h1 h2] at hc'

end GlobalTheory.DiagSqAxes

namespace GlobalTheory.DiagSqAxes

theorem weilIs_diag_sq : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (P : LB (G2 A).left), P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (y : Sp κ ⟶ S) (N : ℕ), 0 < N → (N : κ) ≠ 0 → ∀ (a b : Over.mk y ⟶ A), a ^ N = 1 → b ^ N = 1 → ∀ (c : (Γ((Over.mk y).left, ⊤))ˣ), Out.WeilIs (G2 A) P N (lift a 1) (lift 1 b) c → Out.WeilIs A (P.pull (lift (𝟙 A) (𝟙 A)).left) N a b (c ^ 2) := by
  intro S A _ _ hA P hP h₂ h₁ hsym κ _ _ y N hN hNk a b ha hb c hc
  have hG := GlobalTheory.globalFns_holds
  have hAA : IsAbelianScheme (G2 A) := AbelianSchemeGerms.isAbelianScheme_tensor _ _ hA hA
  have e11 : Out.WeilIs (G2 A) P N (lift a 1) (lift b 1) 1 := by
    have h := weilIs_axis hA hAA hP (lift (𝟙 A) (1 : A ⟶ A)) h₁ κ y N hN hNk a b ha hb
    simpa only [comp_lift, Category.comp_id, MonObj.comp_one] using h
  have e22 : Out.WeilIs (G2 A) P N (lift 1 a) (lift 1 b) 1 := by
    have h := weilIs_axis hA hAA hP (lift (1 : A ⟶ A) (𝟙 A)) h₂ κ y N hN hNk a b ha hb
    simpa only [comp_lift, Category.comp_id, MonObj.comp_one] using h
  have e21 : Out.WeilIs (G2 A) P N (lift 1 a) (lift b 1) c := by
    have hw : LBIso (lbPow P 1) (P.pull (lift (snd A A) (fst A A)).left) :=
      LBIso.trans (GlobalTheory.isLB_lbPow hP 1) hP (pull_isLB hP _) (GlobalTheory.lbIso_lbPow_one hP) hsym
    have h' : Out.WeilIs (G2 A) P N (lift 1 a ≫ lift (snd A A) (fst A A)) (lift b 1 ≫ lift (snd A A) (fst A A)) c := by
      simpa only [comp_lift, lift_fst, lift_snd] using hc
    have h := GlobalTheory.WeilIsogeny.weilIs_pull_hom hG hAA hP hP _ hw h'
    simp only [Nat.cast_one, _root_.mul_one] at h
    exact h
  have r1 := GlobalTheory.DiagPairing.weilIs_mul_left hG hAA hP e11 e21
  have r2 := GlobalTheory.DiagPairing.weilIs_mul_left hG hAA hP hc e22
  rw [lift_mul_lift₂] at r1 r2
  have s := GlobalTheory.DiagPairing.weilIs_mul_left hG hAA hP (GlobalTheory.CommPairing.weilIs_symm hP r1)
    (GlobalTheory.CommPairing.weilIs_symm hP r2)
  have s' := GlobalTheory.CommPairing.weilIs_symm hP s
  rw [lift_mul_lift₂] at s'
  simp only [_root_.mul_one, _root_.one_mul] at s'
  have hd : Out.WeilIs (G2 A) P N (a ≫ lift (𝟙 A) (𝟙 A)) (b ≫ lift (𝟙 A) (𝟙 A)) (c ^ 2) := by
    simp only [comp_lift, Category.comp_id]
    convert s' using 1
    rw [← _root_.mul_inv, inv_inv, pow_two]
  have hD : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB hP _
  have h := GlobalTheory.WeilIsogeny.weilIs_pull_hom hG hA hD hP (lift (𝟙 A) (𝟙 A)) (GlobalTheory.lbIso_lbPow_one hD) hd
  simp only [Nat.cast_one, _root_.mul_one] at h
  exact h

end GlobalTheory.DiagSqAxes
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieMultiplicitiesGeometricPointsDescend
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.LieDesc

theorem lieMult_descend : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (X Y : Scheme.{0}) (π : X ⟶ Y) (sY : Y ⟶ Sp R) (Ga : Type) [Group Ga] (ρ : Ga → (X ⟶ X)) (A : Over X) [GrpObj A] [IsCommMonObj A] (A₀ : Over Y) [GrpObj A₀] [IsCommMonObj A₀] (φ : A.left ⟶ A₀.left) (act : OActN D.O A) (act₀ : OActN D.O A₀), GlobalTheory.ZM.IsGaloisCover Ga ρ π → IsAbelianScheme A → IsAbelianScheme A₀ → IsGrpPullback A A₀ π φ → (∀ c, (act.act c).left ≫ φ = φ ≫ (act₀.act c).left) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ X) (β : R →+* k), x ≫ (π ≫ sY) = spMap β → ∀ i, LieMult (act.toF D) x (β.comp (b.t i)) D.m) → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Y) (β : R →+* k), x ≫ sY = spMap β → ∀ i, LieMult (act₀.toF D) x (β.comp (b.t i)) D.m) := by
  intro p _ D R _ b X Y π sY Ga _ ρ A _ _ A₀ _ _ φ act act₀ hG _ _ hpb hact hX k _ _ x β hx i
  haveI : Surjective π := hG.onto
  haveI : IsFinite π := hG.fin
  obtain ⟨y, rfl⟩ := GlobalTheory.ObjDesc.exists_geomPt_lift π k x
  have hc : ∀ c, ((act.toF D).act c).left ≫ φ = φ ≫ ((act₀.toF D).act c).left := fun c => hact _
  exact (GlobalTheory.LiePull.lieMult_pull _ _ _ A₀ A π φ (act₀.toF D) (act.toF D) hpb hc k y _ D.m).1
    (hX k y β (by rw [← Category.assoc]; exact hx) i)

end GlobalTheory.LieDesc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftsAlongSmallExtensionOfDualNumberLiftingStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftsAlong_smallExtension_of_dualNumber_lifting : ∀ (S : Scheme.{0}) [IsAffine S] (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (U : Over S) [Smooth U.hom] (M : LB (A ⊗ U).left), Fam A M → Inj A M → TanLift A M → SmallLift A M := by
  first | exact @GlobalTheory.DualOpen.smallLift_of_tanLift | exact GlobalTheory.DualOpen.smallLift_of_tanLift | (intros; apply GlobalTheory.DualOpen.smallLift_of_tanLift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleLiftObstructionNaturalStatement
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs GlobalTheory.LBObs GlobalTheory.AbLaw GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundleLiftObstruction_natural : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (R₁ : Type) [CommRing R₁] [Algebra R₀ R₁] (α : Aug I π R₁) (X₀ Z₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (t₀ : Z₀ ⟶ Sp R₀) (S : Sys I π s₀) (S' : Sys I π t₀) (f₀ : Z₀ ⟶ X₀) (h : f₀ ≫ s₀ = t₀ ≫ spMap (RingHom.id R₀)) (l : ∀ T : (Pair f₀)ᵒᵖ, (ofSys S).B ((pairPull h).G.obj T) →ₐ[R] (pairPre S' f₀).B T) (hl : (ofSys S).IsLift (pairPre S' f₀) (pairPull h) l) (hn : (ofSys S).IsNat (pairPre S' f₀) (pairPull h) l) (L : LB X₀) (L' : LB Z₀) (c : GlobalTheory.CatCoh.H2 (ext R₁ (OAff s₀))) (c' : GlobalTheory.CatCoh.H2 (ext R₁ (OAff t₀))), L.IsLB → L'.IsLB → LBIso L' (L.pull f₀) → IsObL S α L c → IsObL S' α L' c' → IsExtendedPullbackDegTwo R₁ h c c' := by
  first | exact @GlobalTheory.LBObs.lineBundleLiftObstruction_natural_alt | exact GlobalTheory.LBObs.lineBundleLiftObstruction_natural_alt | (intros; apply GlobalTheory.LBObs.lineBundleLiftObstruction_natural_alt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCountNearbyPowersSecondBundleLeStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_count_nearby_powers_second_bundle_le : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (b c : ℕ), 0 < b → Regime P D → ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ᶠ M : ℕ in atTop, P.lc 0 (b * M + (M / n : ℕ) - c) 2 ≤ P.lc 0 (b * M - c) 1 + ε * (M : ℝ) ^ (D + 1) := by
  first | exact @GlobalTheory.HSNef.lc_nearby_le | exact GlobalTheory.HSNef.lc_nearby_le | (intros; apply GlobalTheory.HSNef.lc_nearby_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCountRadiusOneLowerBoundAmpleSemiPosStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_count_radius_one_lower_bound_ample_semiPos : AmpleHS → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (a b a' b' : ℤ) (M : HermLB p) (α : ℝ), P.Rep a b M → IsAmpleLB M.B → M.SemiPos D → M.IsSelfInter α → ∀ ε : ℝ, 0 < ε → ∀ᶠ m : ℕ in atTop, (α / (D + 1).factorial - ε) * (m : ℝ) ^ (D + 1) ≤ P.lc (m * a + a') (m * b + b') 1 := by
  first | exact @GlobalTheory.HSNef.lc_one_eventually_ge | exact GlobalTheory.HSNef.lc_one_eventually_ge | (intros; apply GlobalTheory.HSNef.lc_one_eventually_ge <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogCountTwistExpRadiusLePowSuccStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.log_count_twist_exp_radius_le_pow_succ : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p) (b : ℕ) (s t : X.functionField), P.Good D b s t → ∀ c : ℕ, Regime P D → ∃ C : ℝ, ∀ᶠ N : ℕ in atTop, P.lc N (-c) (Real.exp (3 * N)) ≤ C * (N : ℝ) ^ (D + 1) := by
  first | exact @GlobalTheory.HSNef.crude_upper_lc_twist | exact GlobalTheory.HSNef.crude_upper_lc_twist | (intros; apply GlobalTheory.HSNef.crude_upper_lc_twist <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogResolutionMultLtOfConnectednessStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.logResolution_mult_lt_of_connectedness : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → ∀ (η : RatForms p n) (m : ℕ) (G N : CartierDiv X) (Y : Scheme.{0}) [IsIntegral Y] [IsLocallyNoetherian Y] (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y) (F : CartierDiv Y), η ≠ 0 → 0 < m → IsLogRes p n η m G s K B → (∀ z, F.mult z = (pullCart s G - m • K).mult z / (m : ℤ)) → (∀ U : X.Opens, IsAffineOpen U → Subsingleton (cohOn (twist (GlobalTheory.structureModule Y) (toLB (pullCart s N - F))) (s ⁻¹ᵁ U) 1)) → ∀ (y : X) (σ : Y), IsIntegrallyClosed (X.presheaf.stalk y) → (∀ z, z ⤳ y → ∀ E : DivOver p, E.IsAt z → ∀ g, G.IsEqn z g → discrep E η m g ≤ 0) → (pullCart s G - m • K).mult σ = m → s σ ⤳ y → (∀ v w : Y, v ≠ σ → v ⤳ w → σ ⤳ w → s w ⤳ y → (pullCart s G - m • K).mult v < m) → ∀ v : Y, v ≠ σ → s v ⤳ y → (pullCart s G - m • K).mult v < m := by
  first | exact @GlobalTheory.LogResConn.mult_lt_of_connected | exact GlobalTheory.LogResConn.mult_lt_of_connected | (intros; apply GlobalTheory.LogResConn.mult_lt_of_connected <;> assumption)
end

