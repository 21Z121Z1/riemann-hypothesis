import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0030
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0048
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0019
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1455
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0068
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0018
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1491
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1484
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1496
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0890
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1478
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1473
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1533
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1462
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1530
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0916
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0238
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EqNegOfCommute
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0028
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1534
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1471
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0029
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0068
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0083
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0079
import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1097
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.GtActIffEqGtSmul
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0142
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0191
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaConstantEqSumThetaTermsOddMultiple
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1465
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1466

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateCondCongr
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.UPelLevel

variable {F : Type} [Field F] [NumberField F] [IsCMField F]

def TateCond (D : Datum F) (p N : ℕ) {S : Scheme.{0}} (A : Over S) [GrpObj A] (act : OAct (𝓞 F) A) (PP : RigLB A)
    {k : Type} [Field k] (x : Sp k ⟶ S) (lv : D.La → (Over.mk x ⟶ A)) : Prop :=
  ∃ I : TateIsoP D p k (Over.mk x ⟶ A) (fun a g => g ≫ act.act a)
      (fun n g g' c => Out.WeilIs A PP.L n g g' (unitOn c)), ∀ a, lv a = I.ev N a

def IsLevel (D : Datum F) (p N : ℕ) {S : Scheme.{0}} (A : Over S) [GrpObj A] (act : OAct (𝓞 F) A) (PP : RigLB A)
    (T : Over S) (lv : D.La → (T ⟶ A)) : Prop :=
  (∀ a c, lv (a + c) = lv a * lv c) ∧ (∀ a, lv (N • a) = 1) ∧ (∀ (c : 𝓞 F) a, lv (c • a) = lv a ≫ act.act c) ∧
    ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ T.left),
      TateCond D p N A act PP (x ≫ T.hom) fun a => (Over.homMk x rfl : Over.mk (x ≫ T.hom) ⟶ T) ≫ lv a

theorem tateCond_congr (D : Datum F) (p N : ℕ) {S : Scheme.{0}} (A : Over S) [GrpObj A] (act : OAct (𝓞 F) A)
    (PP : RigLB A) {k : Type} [Field k] {x x' : Sp k ⟶ S} (e : x = x') (lv : D.La → (Over.mk x ⟶ A))
    (lv' : D.La → (Over.mk x' ⟶ A))
    (h : ∀ a, (Over.homMk (𝟙 _) (by simp [e]) : Over.mk x' ⟶ Over.mk x) ≫ lv a = lv' a) :
    TateCond D p N A act PP x lv → TateCond D p N A act PP x' lv' := by
  subst e
  have h' : ∀ a, lv a = lv' a := fun a => by
    rw [← h a]
    have : (Over.homMk (𝟙 _) (by simp) : Over.mk x ⟶ Over.mk x) = 𝟙 _ := by ext; simp
    rw [this, Category.id_comp]
  rintro ⟨I, hI⟩
  exact ⟨I, fun a => (h' a).symm.trans (hI a)⟩

end GlobalTheory.UPelLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentFundamentalDomain
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling

namespace GlobalTheory.UnipSpMass

theorem exists_haar_unipSp_mass_one : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (B : Base F E) (d r s : ℕ) (W : Spc F E d), W.IsSkew σ B r s →
    ∀ (j : ℕ) (Y : Matrix (Fin d) (Fin j) E), 1 ≤ j → Function.Injective Y.mulVec →
      (∀ k l, form σ W.J (fun a => Y a k) (fun a => Y a l) = 0) →
      ∃ (ν : Measure (GlobalTheory.ThKLiftCusp.unipSp σ W Y)) (𝓕 : Set (GlobalTheory.ThKLiftCusp.unipSp σ W Y)), ν.IsHaarMeasure ∧
        IsFundamentalDomain ((ratU σ W.J).subgroupOf (GlobalTheory.ThKLiftCusp.unipSp σ W Y)) 𝓕 ν ∧ ν 𝓕 = 1 := by
  intro F E _ _ _ _ _ σ hcm B d r s W hW j Y _ hY hiso
  have hσ : ∀ x, σ (σ x) = x := GlobalTheory.SiegelSet.sigma_sigma hcm
  obtain ⟨c, hc, hcs⟩ := GlobalTheory.CMImag.exists_imag_ne_zero F E σ hcm
  have hJ : IsHermND σ (c • W.J.map σ) := GlobalTheory.ThK.SqIntHerm.isHermND_smul_map F E σ B d W r s hW c hc hcs
  have hC : GlobalTheory.UAut.IsIsoCols σ (c • W.J.map σ) Y := by
    refine ⟨Matrix.mulVec_injective_iff.1 hY, ?_⟩
    ext k l
    have h := congrArg (fun x => c * σ x) (hiso k l)
    simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, map_zero, mul_zero] at h
    rw [Matrix.zero_apply, ← h]
    simp only [Formalism.UG.cT, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.zero_apply, Finset.sum_mul, Finset.mul_sum, RingHom.coe_coe]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => by ring
  have hmem := GlobalTheory.UnipMatch.mem_unipSp_iff F E σ hσ B d W r s hW c hc j Y hiso
  have hrat := GlobalTheory.RatCorr.ratU_iff_ratPts F E σ hσ d W.J c hc
  set e := GlobalTheory.ThK.SquareIntegrability.toGAd hσ W.J hc with he
  obtain ⟨hTG, hLC, hSC, hT2⟩ := GlobalTheory.UnipMass.topUA σ W.J
  haveI := hTG
  haveI := hLC
  haveI := hSC
  haveI := hT2
  haveI : BorelSpace (UA σ W.J) := ⟨rfl⟩
  haveI : LocallyCompactSpace (GlobalTheory.SiegelSet.unipRad σ (c • W.J.map σ) Y) :=
    GlobalTheory.UAut.locallyCompact_unipRad hcm hJ hC
  obtain ⟨K', hK', hcov'⟩ := GlobalTheory.UAut.cocompact_unipRad hcm hJ hC
  have hec : Continuous e := continuous_subtype_val.subtype_mk _
  have hes : Continuous e.symm := continuous_subtype_val.subtype_mk _
  let eH : GlobalTheory.ThKLiftCusp.unipSp σ W Y ≃ₜ GlobalTheory.SiegelSet.unipRad σ (c • W.J.map σ) Y :=
    { toFun := fun x => ⟨e x, (hmem x).1 x.2⟩
      invFun := fun y => ⟨e.symm y, (hmem _).2 (by rw [e.apply_symm_apply]; exact y.2)⟩
      left_inv := fun x => by ext; simp
      right_inv := fun y => by ext; simp
      continuous_toFun := (hec.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (hes.comp continuous_subtype_val).subtype_mk _ }
  haveI : LocallyCompactSpace (GlobalTheory.ThKLiftCusp.unipSp σ W Y) := eH.isClosedEmbedding.locallyCompactSpace
  haveI := GlobalTheory.UnipMass.countable_ratU' σ W.J (GlobalTheory.ThKLiftCusp.unipSp σ W Y)
  haveI := GlobalTheory.T.discrete_rational_points_subgroup F E σ d W.J (GlobalTheory.ThKLiftCusp.unipSp σ W Y)
  refine GlobalTheory.T.cocompact_lattice_unit_covolume _ _ (eH ⁻¹' K') (eH.isCompact_preimage.2 hK') fun g => ?_
  obtain ⟨γ', hγ', hK⟩ := hcov' (eH g)
  refine ⟨⟨eH.symm γ', ?_⟩, ?_⟩
  · rw [Subgroup.mem_subgroupOf]
    show e.symm (γ' : _) ∈ ratU σ W.J
    rw [hrat, MulEquiv.apply_symm_apply]
    exact Subgroup.mem_subgroupOf.1 hγ'
  · show eH (eH.symm γ' * g) ∈ K'
    have : eH (eH.symm γ' * g) = γ' * eH g := by
      apply Subtype.ext
      show e (e.symm (γ' : _) * (g : _)) = (γ' : _) * e g
      rw [map_mul, MulEquiv.apply_symm_apply]
    rw [this]
    exact hK

end GlobalTheory.UnipSpMass
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentFundamentalDomainIntegralStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThKCtFin GlobalTheory.TorFin

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unipotent_fundamental_domain_integral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E), IsCMExt F E σ → ∀ (d r s : ℕ) (W : Spc F E d), W.IsSkew σ B r s → ∀ (hσ : ∀ x, σ (σ x) = x) (c : E) (hc : c ≠ 0), σ c = -c → ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ f : UA σ W.J → ℂ, ∀ (μ : Measure (unip σ W H')) (𝓕 : Set (unip σ W H')), μ.IsHaarMeasure → IsFundamentalDomain ((ratU σ W.J).subgroupOf (unip σ W H')) 𝓕 μ → μ 𝓕 = 1 → ∀ cc : GAd σ (c • W.J.map σ) → ℂ, IsConstTerm σ (c • W.J.map σ) (Matrix.of fun i (_ : Fin 1) => H'.x i) (fun x => f ((toGAd hσ W.J hc).symm x)) cc → ∀ g : UA σ W.J, ∫ u in 𝓕, f (u.1 * g) ∂μ = cc (toGAd hσ W.J hc g) := by
  first | exact @GlobalTheory.CtTransp.setIntegral_unip_eq_constTerm | exact GlobalTheory.CtTransp.setIntegral_unip_eq_constTerm | (intros; apply GlobalTheory.CtTransp.setIntegral_unip_eq_constTerm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitriangularChartMemDomainSmallBall
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up

namespace GlobalTheory.ChartDomain

open NumberField in

theorem _root_.GlobalTheory.ChartDomain.cpt_mem_dom_of_norm_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) (x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r) (z : _root_.ReciprocityTheory.L2DbarEstimates.V (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nd X)), _root_.ReciprocityTheory.ChartRestriction.G.AR.Up.IsOrth X x →
    ‖z‖ ≤ 1 / (100 * (r : ℝ) ^ 2) → _root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.cpt X x z ∈ X.dom := by
  intro E _ _ _ r X x z hx hz
  have hsmall : (r : ℝ) ^ 2 * ‖z‖ ≤ 1 / 100 := by
    by_cases hr : (r : ℝ) = 0
    · simp [hr]
    · have hpos : 0 < (r : ℝ) ^ 2 := by positivity
      calc (r : ℝ) ^ 2 * ‖z‖ ≤ (r : ℝ) ^ 2 * (1 / (100 * (r : ℝ) ^ 2)) :=
            mul_le_mul_of_nonneg_left hz hpos.le
        _ = 1 / 100 := by field_simp
  exact (_root_.GlobalTheory.dmin_rmul_near_one X x hx (_root_.ReciprocityTheory.ChartRestriction.G.AR.Inst.nmat X z) (norm_nonneg z) hsmall
    (fun τ a b => _root_.GlobalTheory.ChartNearOne.nmat_entry_le X z τ a b)).1

end GlobalTheory.ChartDomain
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacuumCharacterPositiveDefiniteSource
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct Kronecker ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.VacuumCharacter

variable {D : D7}

theorem vacuum_character : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → IsInfFam θ → S.SigOK → T.SigOK → ∀ (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ), (∀ τ, IsCartanInv (gramAt D S τ) 1) → (∀ τ, IsCartanInv (gramAt D T τ) (sT τ)) → ∀ (a b : D.what₂.Tau → ℚ), (∀ τ, HasInfExp D χS τ (a τ)) → (∀ τ, HasInfExp D χT τ (b τ)) → ∀ (x₁ x₂ x₃ : D.what₂.Tau → ℤ), (∀ τ, (x₁ τ : ℚ) = a τ + (S.rank : ℚ) / 2) → (∀ τ, (x₂ τ : ℚ) = a τ - (S.rank : ℚ) / 2) → (∀ τ, (x₃ τ : ℂ) = -((sT τ).trace / 2 + (b τ : ℂ))) → ∀ f, IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO 1 (sT τ)) f) → ∀ g ∈ GinfC S, ∀ h ∈ GinfC T, (∀ τ, sT τ * compAt θ τ (Formalism.L2.Theta.mt T h) = compAt θ τ (Formalism.L2.Theta.mt T h) * sT τ) → om (g, h) f = (∏ τ, ((1 / 2 : ℂ) • (1 + sT τ) * compAt θ τ (Formalism.L2.Theta.mt T h) + (1 / 2 : ℂ) • (1 - sT τ)).det ^ x₁ τ * ((1 / 2 : ℂ) • (1 - sT τ) * compAt θ τ (Formalism.L2.Theta.mt T h) + (1 / 2 : ℂ) • (1 + sT τ)).det ^ x₂ τ * (compAt θ τ (Formalism.L2.Theta.mt S g)).det ^ x₃ τ) • f := by
  intro D ψ θ S T χS χT om hW hθ _ _ sT hS hT a b ha hb x₁ x₂ x₃ h1 h2 h3 f hf hv g hg h hh hc
  obtain ⟨η, e1, e2, e3, e4⟩ := GlobalTheory.T.exists_unramifiedHeckeChar_halfExponent_restrict_quadratic D
  have hdet : ∀ {k : ℕ} {G s : Matrix (Fin k) (Fin k) ℂ}, IsCartanInv G s → G.det ≠ 0 := fun {k G s} hG => by
    have := hG.2.2.det_pos.ne'
    rw [Matrix.det_mul] at this
    exact left_ne_zero_of_mul this
  obtain ⟨x, hx, hxv⟩ := exists_root hθ S (fun τ => hdet (hS τ)) g hg
  obtain ⟨y, hy, hyv⟩ := exists_root hθ T (fun τ => hdet (hT τ)) h hh
  choose p hp hd using fun τ => detPlus_one (n := S.rank) (sT τ) (hT τ).1
  rw [GlobalTheory.T.weilDatum_realPlaces_fockVacuum_character D ψ hW.std S T θ hθ χS χT om η ⟨e1, e4, e3, e2⟩ hW (fun _ => 1) sT hS hT g hg h hh
    (fun τ => by rw [one_mul, mul_one]) hc x y hx hy f hf hv]
  congr 1
  have hb' : ∀ τ, ((-x₃ τ - p τ : ℤ) : ℚ) = b τ - T.rank / 2 := fun τ => by
    have := h3 τ
    rw [hp] at this
    apply Rat.cast_injective (α := ℂ)
    push_cast
    linear_combination -this
  rw [Circle.coe_mul, Circle.coe_inv,
    hxv _ (fun τ => -x₃ τ - p τ) (fun τ => by rw [hb']; exact hasInfExp_twist (hb τ) (e2 τ) _),
    hyv _ x₂ (fun τ => by rw [h2]; exact hasInfExp_twist (ha τ) (e2 τ) _),
    ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun τ _ => ?_
  obtain ⟨d1, d2⟩ := hd τ (compAt θ τ (Formalism.L2.Theta.mt S g⁻¹)) (compAt θ τ (Formalism.L2.Theta.mt T h)) (hc τ)
  have inv : ∀ (V : HSp D) (k : GA D V),
      (compAt θ τ (Formalism.L2.Theta.mt V k)).det * (compAt θ τ (Formalism.L2.Theta.mt V k⁻¹)).det = 1 := fun V k => by
    rw [det_compAt, det_compAt, ← map_mul, ← map_mul, ← Matrix.det_mul]
    unfold Formalism.L2.Theta.mt
    rw [← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, Matrix.det_one, map_one, map_one]
  have g0 := left_ne_zero_of_mul_eq_one (inv S g)
  have h0 := left_ne_zero_of_mul_eq_one (inv T h)
  rw [d2] at h0
  have h0' := left_ne_zero_of_mul h0
  have e : x₁ τ = x₂ τ + S.rank := by
    have : (x₁ τ : ℚ) = x₂ τ + S.rank := by rw [h1, h2]; ring
    exact_mod_cast this
  have alg : ∀ (A B G : ℂ) (u v : ℤ) (n k : ℕ), A ≠ 0 → G ≠ 0 →
      (G ^ (-v - k))⁻¹ * (A * B) ^ u * (A ^ n * G⁻¹ ^ k) = A ^ (u + n) * B ^ u * G ^ v := by
    intro A B G u v n k hA hG
    rw [mul_zpow, zpow_add₀ hA, zpow_sub₀ hG, _root_.zpow_neg, zpow_natCast, zpow_natCast, inv_pow]
    have := zpow_ne_zero v hG
    have := pow_ne_zero k hG
    field_simp
  rw [d1, d2, eq_inv_of_mul_eq_one_right (inv S g), e]
  exact alg _ _ _ _ _ _ _ h0' g0

end GlobalTheory.VacuumCharacter

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacuumEigenAtAllPlacesStatement
section
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.FinComm GlobalTheory.VacLine

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vacuum_eigen_at_all_places : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ), M.IsGood ψ →
    ∀ c : Pl F → Matrix (Fin n) (Fin d) (AE F E) → ℂ,
    (∀ v, ∀ γ ∈ latAtV X W v, ∀ f : SInf F (Fin n × Fin d),
      M.co.rho ψ γ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f M.vac) = c v γ • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f M.vac) →
    ∀ v, ∀ γ ∈ latAtV X W v, locOp ψ v (locPt v (M.co.e γ)) (M.vac v) = c v γ • M.vac v := by
  first | exact @GlobalTheory.VacEig.vac_eig | exact GlobalTheory.VacEig.vac_eig | (intros; apply GlobalTheory.VacEig.vac_eig <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacuumExponentSum
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct Kronecker ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitVacSum

section Lin

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem idem_trace_det (P : Matrix ι ι ℂ) (hP : P * P = P) :
    P.trace = P.rank ∧ ∀ u : ℂ, (u • P + (1 - P)).det = u ^ P.rank := by
  have hi : IsIdempotentElem (Matrix.toLin' P) := by
    unfold IsIdempotentElem
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, hP]
  have hp : LinearMap.IsProj (LinearMap.range (Matrix.toLin' P)) (Matrix.toLin' P) :=
    LinearMap.IsIdempotentElem.isProj_range _ hi
  have hr : Module.finrank ℂ (LinearMap.range (Matrix.toLin' P)) = P.rank := rfl
  refine ⟨?_, fun u => ?_⟩
  · rw [← Matrix.trace_toLin'_eq, hp.trace, hr]
  · rw [← LinearMap.det_toLin']
    have e := hp.eq_conj_prodMap
    set c := (Submodule.prodEquivOfIsCompl _ _ hp.isCompl)
    have e2 : Matrix.toLin' (u • P + (1 - P)) = c.conj (LinearMap.prodMap (u • LinearMap.id) LinearMap.id) := by
      have : LinearMap.prodMap (u • LinearMap.id) LinearMap.id =
          u • LinearMap.prodMap (LinearMap.id : LinearMap.range (Matrix.toLin' P) →ₗ[ℂ] _) (0 : LinearMap.ker (Matrix.toLin' P) →ₗ[ℂ] _)
            + (1 - LinearMap.prodMap LinearMap.id 0) := by
        refine LinearMap.ext fun x => ?_
        ext <;> simp
      rw [this, map_add, map_add, map_smul, map_smul, map_sub, map_sub, ← e, Matrix.toLin'_one]
      congr 2
      exact (LinearEquiv.conj_id c).symm
    rw [e2, LinearEquiv.conj_apply, LinearMap.comp_assoc, LinearMap.det_conj, LinearMap.det_prodMap, LinearMap.det_smul,
      LinearMap.det_id, LinearMap.det_id, hr, mul_one, mul_one]

theorem half_idem {s : Matrix ι ι ℂ} (hs : s * s = 1) :
    ((1 / 2 : ℂ) • (1 + s)) * ((1 / 2 : ℂ) • (1 + s)) = (1 / 2 : ℂ) • (1 + s) := by
  simp only [Matrix.smul_mul, Matrix.mul_smul, mul_add, add_mul, hs, mul_one, one_mul]
  module

theorem le_rank_half {m : ℕ} {G s t : Matrix ι ι ℂ} (hpos : (G * s).PosDef) (ht : t = s ∨ t = -s)
    (B : Matrix ι (Fin m) ℂ) (C : Matrix (Fin m) ι ℂ) (hC : C * B = 1) (hB : Bᴴ * G * B = 0) :
    m ≤ ((1 / 2 : ℂ) • (1 + t)).rank := by
  refine le_trans ?_ (Matrix.rank_mul_le_left _ B)
  have hinj : Function.Injective (((1 / 2 : ℂ) • (1 + t)) * B).mulVecLin := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    have h1 : B *ᵥ a + t *ᵥ (B *ᵥ a) = 0 := by
      rw [Matrix.mulVecLin_apply, ← Matrix.mulVec_mulVec, Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.one_mulVec] at ha
      exact (smul_eq_zero.1 ha).resolve_left (by norm_num)
    have h2 : star (B *ᵥ a) ⬝ᵥ G *ᵥ (B *ᵥ a) = 0 := by
      rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hB,
        Matrix.zero_mulVec, dotProduct_zero]
    have h3 : star (B *ᵥ a) ⬝ᵥ (G * s) *ᵥ (B *ᵥ a) = 0 := by
      rw [← Matrix.mulVec_mulVec]
      rcases ht with rfl | rfl
      · rw [eq_neg_of_add_eq_zero_right h1, Matrix.mulVec_neg, dotProduct_neg, h2, neg_zero]
      · rw [Matrix.neg_mulVec, add_neg_eq_zero] at h1
        rw [← h1, h2]
    have h4 : B *ᵥ a = 0 := by
      by_contra h
      exact (hpos.dotProduct_mulVec_pos h).ne' h3
    rw [← Matrix.one_mulVec a, ← hC, ← Matrix.mulVec_mulVec, h4, Matrix.mulVec_zero]
  unfold Matrix.rank
  rw [LinearMap.finrank_range_of_inj hinj]
  simp

theorem trace_eq_zero {m : ℕ} {G s : Matrix ι ι ℂ} (hs : s * s = 1) (hpos : (G * s).PosDef) (hm : 2 * m = Fintype.card ι)
    (B : Matrix ι (Fin m) ℂ) (C : Matrix (Fin m) ι ℂ) (hC : C * B = 1) (hB : Bᴴ * G * B = 0) : s.trace = 0 := by
  have a1 := le_rank_half hpos (Or.inl rfl) B C hC hB
  have a2 := le_rank_half hpos (Or.inr rfl) B C hC hB
  have b1 := (idem_trace_det _ (half_idem hs)).1
  have b2 := (idem_trace_det _ (half_idem (s := -s) (by rw [neg_mul_neg, hs]))).1
  rw [Matrix.trace_smul, Matrix.trace_add, Matrix.trace_one, ← hm, smul_eq_mul] at b1 b2
  rw [Matrix.trace_neg] at b2
  have c : ((((1 / 2 : ℂ) • (1 + s)).rank + ((1 / 2 : ℂ) • (1 + -s)).rank : ℕ) : ℂ) = (2 * m : ℕ) := by
    rw [Nat.cast_add, ← b1, ← b2]; ring
  have c' := Nat.cast_injective c
  have d : ((1 / 2 : ℂ) • (1 + s)).rank = m := by omega
  rw [d] at b1
  push_cast at b1
  linear_combination 2 * b1

end Lin

theorem detPlus_one {m n : ℕ} (sS : Matrix (Fin n) (Fin n) ℂ) (sT : Matrix (Fin m) (Fin m) ℂ) :
    GlobalTheory.WeilParts.detPlus sS sT ((1 : ℂ) • 1) ((1 : ℂ) • 1) = 1 := by
  unfold GlobalTheory.WeilParts.detPlus
  rw [one_smul, one_smul, Matrix.transpose_one, Matrix.one_kronecker_one, mul_one,
    show (1 / 2 : ℂ) • (1 + sT ⊗ₖ sSᵀ) + (1 / 2 : ℂ) • (1 - sT ⊗ₖ sSᵀ) = 1 by module, Matrix.det_one]

variable {D : D7} {θ : InfFam D}

end GlobalTheory.SplitVacSum

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacuumUniqueProductEigenStatement
section
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.FinComm GlobalTheory.VacLine

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.vacuum_unique_product_eigen : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ)
    (vac : ∀ v : Pl F, (κ → Fv F v) → ℂ) (Q : ∀ v : Pl F, Set (((κ → Fv F v) × (κ → Fv F v)) × ℂ)),
    (∀ v, vac v ∈ SB (κ → Fv F v)) → (∀ v, vac v ≠ 0) → (∀ᶠ v in cofinite, vac v = indO v) →
    (∀ v, ∀ φ ∈ SB (κ → Fv F v), (∀ q ∈ Q v, locOp ψ v q.1 φ = q.2 • φ) → ∃ a : ℂ, φ = a • vac v) →
    ∀ g ∈ SB (κ → Af F), (∀ v, ∀ q ∈ Q v, finOp ψ v q.1 g = q.2 • g) → ∃ a : ℂ, g = a • vacProd vac := by
  first | exact @GlobalTheory.VacFactor.eq_smul_vacProd | exact GlobalTheory.VacFactor.eq_smul_vacProd | (intros; apply GlobalTheory.VacFactor.eq_smul_vacProd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuePulledBackSectionEqImageFieldExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.ZH
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
noncomputable section
namespace GlobalTheory.ValuePullback

theorem valAt_abPull : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (t : SecA A (FractionRing R) k) (x : TFK (R := R) (FractionRing R) ⟶ A.A) (fr : FrAt x) (x' : TFK (R := R) F ⟶ A.A) (fr' : FrAt x'), x'.left = spMap (algebraMap (FractionRing R) F) ≫ x.left → fr.IsGen → (∀ z J, Good A.L z J → val fr' (𝟙 _) z J = val fr (spMap (algebraMap (FractionRing R) F)) z J) → ∀ c : FractionRing R, ValAt t x fr c → ValAt (GlobalTheory.TorsionExt.abPull (FractionRing R) F A k t) x' fr' (algebraMap (FractionRing R) F c) := by
  intro R _ _ A F _ _ k t x fr x' fr' hx _ hv c h z J hJ
  obtain rfl : x' = GlobalTheory.TorsionExt.fieldMap (R := R) (FractionRing R) F ≫ x := Over.OverMorphism.ext hx
  let p : (TFK (R := R) F).left ⟶ (TFK (R := R) (FractionRing R)).left :=
    (GlobalTheory.TorsionExt.fieldMap (R := R) (FractionRing R) F).left
  have e : ptSecT A.A (GlobalTheory.TorsionExt.fieldMap (R := R) (FractionRing R) F ≫ x) ≫
      GlobalTheory.TorsionExt.fieldMap (R := R) (FractionRing R) F ▷ A.A =
      GlobalTheory.TorsionExt.fieldMap (R := R) (FractionRing R) F ≫ ptSecT A.A x := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [ptSecT]
  have e' : (ptSecT A.A (GlobalTheory.TorsionExt.fieldMap (R := R) (FractionRing R) F ≫ x)).left ≫
      (GlobalTheory.TorsionExt.fieldMap (R := R) (FractionRing R) F ▷ A.A).left = p ≫ (ptSecT A.A x).left :=
    congrArg (fun q => q.left) e
  refine (GlobalTheory.FieldBaseChange.sval_pullOver _ _ _ _ hJ).trans ?_
  rw [e']
  obtain ⟨hJ', h₁, -, -⟩ := GlobalTheory.values_natural _ _ _ _ A.L (Fin 1)
    (fun _ => (snd (TFK (R := R) (FractionRing R)) A.A).left) (fun _ => (k : ℤ)) (ptSecT A.A x).left p z J hJ
  obtain ⟨-, -, h₂, h₃⟩ := GlobalTheory.values_natural _ _ _ _ A.L (Fin 1)
    (fun _ => x.left) (fun _ => (k : ℤ)) (𝟙 _) p z J hJ
  refine (h₁ _).trans ((congrArg (p.stalkMap z).hom (h (p z) _ hJ')).trans ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) ?_ ?_)))
  · refine (h₃ _).symm.trans ?_
    rw [Category.comp_id]
    refine (gs_eq p z ⊤ trivial _).trans (Eq.trans ?_ (gs_eq (𝟙 _) z ⊤ trivial _).symm)
    refine congrArg _ ?_
    exact (congrArg (fun q => q.hom c)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap (FractionRing R) F)))).symm
  · refine (h₂ _).symm.trans (congrArg Units.val ?_)
    rw [Category.comp_id]
    have p₁ : val (powFrame A.A A.L x fr k) p z J = val fr p z J ^ (k : ℤ) := map_zpow _ _ _
    have p₂ : val (powFrame A.A A.L _ fr' k) (𝟙 _) z J = val fr' (𝟙 _) z J ^ (k : ℤ) := map_zpow _ _ _
    exact p₁.trans ((congrArg (· ^ (k : ℤ)) (hv z J hJ).symm).trans p₂.symm)

end GlobalTheory.ValuePullback
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepFinitePeriodicityPolynomialHeightStatement
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
open GlobalTheory.ArchDecay
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRep_finite_periodicity_polynomial_height : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ Φ ∈ schA F (Fin n × Fin d), ∃ (C : ℝ) (k : ℕ), ∀ g h, ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ C * ((ht g : ℝ) * ht h) ^ k ∧ Per F m (om (g, h) Φ) := by
  first | exact @GlobalTheory.ArchDecay.per_om_level | exact GlobalTheory.ArchDecay.per_om_level | (intros; apply GlobalTheory.ArchDecay.per_om_level <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepMovedArchimedeanCoordsPolynomialHeightStatement
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
open scoped Classical
open GlobalTheory.ArchDecay

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilRep_moved_archimedean_coords_polynomial_height : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∃ (C : ℝ) (k : ℕ), ∀ (g : UA σ X.J) (h : UA σ W.J) (ζ : (Fin n × Fin d → mixedEmbedding.mixedSpace F) × (Fin n × Fin d → mixedEmbedding.mixedSpace F)), ‖movI M (g, h) ζ‖ ≤ C * ((ht g : ℝ) * ht h) ^ k * ‖ζ‖ := by
  first | exact @GlobalTheory.ArchDecay.movI_size | exact GlobalTheory.ArchDecay.movI_size | (intros; apply GlobalTheory.ArchDecay.movI_size <;> assumption)
end

