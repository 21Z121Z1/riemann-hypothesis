import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2950
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0946
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0015
import ReciprocityTheory.L2DbarEstimates.LeviForms.EventuallyDifferentiableAtOfContDiffAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2512
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2907
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2703
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2693
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2983
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsArBaseAway
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3028
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0072
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NefFibOfIsGenerated
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1111
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2733
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2751
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2970
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2905
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0020
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2362
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3022
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0077
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0030
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2747
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3010
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2707
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2336
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2730
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3029
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0085
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopologicalKrullDimEqSucc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1333
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0019
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0002

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiPosRegPull
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Weight

open ReciprocityTheory.L2DbarEstimates (V leviV)

theorem semiPosReg_pull : ∀ (k : Type) [CommRing k] (X Y : Scheme.{0}) (p : X ⟶ Sp k) (q : Y ⟶ Sp k) (σ : k →+* ℂ) (π : Y ⟶ X) (hπ : π ≫ p = q) (D D' : ℕ), SmoothOfRelativeDimension D p → ∀ (B : LB X) (φ : Weight p σ B), φ.IsCInf → φ.SemiPosReg D → (φ.pull π hπ).SemiPosReg D' := by
  intro k _ X Y p q σ π hπ D D' hs B φ hC hSP
  haveI := hs
  intro i c y hy ξ
  set m := PtsOver.map π hπ (spMap σ)
  have hm : ∀ z, (m z).1 = z.1 ≫ π := fun _ => rfl
  obtain ⟨c0, h0⟩ := AlgChart.exists_mem_source (p := p) (σ := σ) (D := D) (m y)
  have him : m y ∈ ptsIn p σ (B.U (i PUnit.unit)) :=
    mem_of_mem_linComb (m := fun _ => m y) (fun _ => rfl) hy.2 PUnit.unit
  set F : V D' → V D := c0.e ∘ m ∘ c.e.symm with hFdef
  set U := c.e.target ∩ c.e.symm ⁻¹' (m ⁻¹' c0.e.source)
  have hU : IsOpen U := GlobalTheory.ChartGlue.isOpen_over c.e (c0.e.open_source.preimage (continuous_of_comp hm))
  have hyU : c.e y ∈ U := GlobalTheory.ChartGlue.mem_over c.e hy.1 h0
  have hF0 : DifferentiableOn ℂ F U := AlgChart.holo_map hm c c0
  have hF : ContDiffOn ℂ 2 F U := (contDiffOn_piLp 2).2 fun a =>
    (ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn D' _ U hU
      (differentiableOn_euclidean.1 hF0 a)).of_le (by norm_cast)
  have hFy : F (c.e y) = c0.e (m y) := by
    simp only [hFdef, Function.comp_apply, c.e.left_inv hy.1]
  set g : V D → ℂ := fun v => (φ.φ (i PUnit.unit) (c0.e.symm v) : ℂ) with hgdef
  have hg : ContDiffAt ℝ 2 g (F (c.e y)) := hFy ▸
    Complex.ofRealCLM.contDiff.contDiffAt.comp _ (hC.contDiffAt c0 h0 him)
  have e : (fun v => ((φ.pull π hπ).φ i (c.e.symm v) : ℂ)) =ᶠ[𝓝 (c.e y)] g ∘ F := by
    filter_upwards [hU.mem_nhds hyU] with v hv
    have := Weight.pull_φ φ π hπ i (c.e.symm v)
    simp only [g, hFdef, Function.comp_apply, c0.e.left_inv hv.2]
    exact congrArg _ this
  rw [ReciprocityTheory.L2DbarEstimates.leviV_congr e,
    ReciprocityTheory.ChartRestriction.G.AR.Up.RGF.gc_leviV_comp D' D g F U hU _ hyU hF hg ξ, hFy]
  exact hSP (i PUnit.unit) c0 (m y) ⟨h0, him⟩ _

end GlobalTheory.Weight
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SharpRefinementOddPrimeLocalization
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Sep.E8Fibration

theorem eighthPowerFibre_thetaObj : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (gQ : ℕ), ∃ (J : Type) (_ : Finite J)
    (Mat : J → Matrix (Fin (2 * (8 * gQ))) (Fin (2 * (8 * gQ))) ℤ) (κ : ℕ) (w w' : J),
  ∀ (l : ℕ), l.Prime → Odd l → ∀ j : ℕ, 1 ≤ j →
  ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → IsUnit (l : V₁) →
  ∀ (Q : Data V), Q.g = gQ → ∀ (ρ : V →+* V₁), Function.Injective ρ → ∀ (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X),
  SharpRef W Q ρ D e →
  ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ →
  ∃ (bT : TBase k₀ ((l ^ j) ^ 2)) (t : TObj (8 * gQ) ((l ^ j) ^ 2) J bT (spMap k₀.subtype))
    (ψ : ((Over.pullback (spMap ev)).obj D.P.A).left ⟶ t.A.left),
    t.Shape Mat κ ∧ t.Prim w w' ∧
    IsGrpPullback ((Over.pullback (spMap ev)).obj D.P.A) t.A (𝟙 _) ψ ∧
    LBIso (D.P.L.pull (pullback.fst D.P.A.hom (spMap ev))) (t.L.pull ψ) ∧
    ∀ (y : Over.mk (spMap ev) ⟶ D.P.A), y ^ ((l ^ j) ^ 2) = 1 →
      ∀ q : Sp K ⟶ ((Over.pullback (spMap ev)).obj D.P.A).left,
      q ≫ pullback.fst D.P.A.hom (spMap ev) = y.left → q ≫ pullback.snd D.P.A.hom (spMap ev) = 𝟙 _ →
      ∃ a, q ≫ ψ = (t.lab a).left := by
  intro W hW gQ
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.e8_act_linComb_relAmple W hW
  obtain ⟨Mat, hMat⟩ := GlobalTheory.T.e8_fibration_algebraically_closed_field W hW gQ
  refine ⟨Fin 2, inferInstance, Mat, κ, 0, 1, ?_⟩
  intro l hl hlo j hj V V₁ _ _ _ _ _ hCN hlu Q hQ ρ hρ D e hS K _ _ ev k₀ hk₀
  obtain ⟨P', ψ, B, _, M, pr, hg, hψ, hL, hB, hpr, hE, hpt⟩ := GlobalTheory.T.exists_polarized_specialization_field W gQ V V₁ Q hQ ρ hρ D e hS K ev
  haveI : IsCommMonObj B := hB.1.comm
  choose act hact1 hact2 using fun i : Fin 2 => GlobalTheory.T.exists_eighth_power_endomorphism_acting_by_matrix _ _ _ pr hpr (E8Fibration.actMat W i)
  have hlK : (l : K) ≠ 0 := by
    have := hlu.map ev
    rw [map_natCast] at this
    exact this.ne_zero
  obtain ⟨bT, pt, htor, hbij, hpair, hsh⟩ := hMat l hl hlo j hj K k₀ hk₀ hlK P' hg B M pr hB hpr hE act hact1 hact2
  let t : TObj (8 * gQ) ((l ^ j) ^ 2) (Fin 2) bT (spMap k₀.subtype) :=
    { A := P'.A, grp := P'.grp, ab := P'.isAb, dim := hg ▸ P'.smoothDim, L := P'.L, isLB := P'.isLB,
      rigid := P'.rigid, sym := P'.sym, ample := P'.ample, ktriv := P'.ktriv, pt := pt, torsion := htor,
      bij := hbij, pairing := hpair, act := act, hom := hact1 }
  refine ⟨bT, t, ψ, ?_, ?_, hψ, hL, ?_⟩
  · exact fun a => ⟨hsh a, hκ gQ K P' B M pr hB hpr hE act hact1 hact2 a⟩
  · exact GlobalTheory.T.e8_act_prod_eq_one W hW gQ K P' B M pr hB hpr hE act hact1 hact2
  · intro y hy q hq1 hq2
    obtain ⟨y', hy'1, hy'2⟩ := hpt _ y hy q hq1 hq2
    obtain ⟨c, hc, -⟩ := hbij K (𝟙 _) y' hy'2
    refine ⟨c, ?_⟩
    rw [← hy'1, ← hc]
    have h0 : (Over.homMk (𝟙 (Sp K)) (by simp) : Over.mk (𝟙 (Sp K)) ⟶ Out.baseOver (Sp K)) = 𝟙 _ := by
      ext; simp
    simp only [h0, Category.id_comp]
    rfl

end GlobalTheory.Poinc.Sep.E8Fibration
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortGeneratorSectionsSmallShiftedFubiniStudyStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.shortGenerator_sections_small_shifted_fubiniStudy : ∀ (K V Ω : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Field Ω] [Algebra K Ω] (Nm : (K →+* ℂ) → V → ℝ) (W : Submodule (𝓞 K) V) (ev : V →ₗ[K] Ω) (D : ℕ) (X : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp (𝓞 K)) (L : GlobalTheory.HermLB p) (ψ : Ω →+* X.functionField) (s : W → L.B.Sec), GlobalTheory.ImageModel.IsModelOf Nm W ev D p L ψ s → ev ≠ 0 → ∀ (n : ℕ) (w : Fin n → V) (abelian₂ t : ℝ), GlobalTheory.CompHt.IsShortGen Nm W w abelian₂ → Real.log abelian₂ ≤ t → ∀ (j : Fin n) (hj : w j ∈ W), s ⟨w j, hj⟩ ∈ (L.shift (fun _ => t) (fun _ => rfl)).smallSec := by
  first | exact @GlobalTheory.ImageModel.smallSec_shift_of_isShortGen | exact GlobalTheory.ImageModel.smallSec_shift_of_isShortGen | (intros; apply GlobalTheory.ImageModel.smallSec_shift_of_isShortGen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelClassifiedAtPrimeSpreadsBasicOpenStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelClassified_at_prime_spreads_basicOpen : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n), ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (β : cycAway n →+* R) (c : SiegPre g n (zetaAway n) (spMap β)) (𝔭 : Ideal R) [𝔭.IsPrime], c.Principal → (∀ c' : SiegPre g n (zetaAway n) (spMap ((algebraMap R (Localization.AtPrime 𝔭)).comp β)), SiegPB c' c (spMap (algebraMap R (Localization.AtPrime 𝔭))) → ∃ f : Sp (Localization.AtPrime 𝔭) ⟶ F.X, f ≫ F.s = spMap ((algebraMap R (Localization.AtPrime 𝔭)).comp β) ∧ SiegPB c' F.univ f) → ∃ r ∉ 𝔭, ∀ c' : SiegPre g n (zetaAway n) (spMap ((algebraMap R (Localization.Away r)).comp β)), SiegPB c' c (spMap (algebraMap R (Localization.Away r))) → ∃ f : Sp (Localization.Away r) ⟶ F.X, f ≫ F.s = spMap ((algebraMap R (Localization.Away r)).comp β) ∧ SiegPB c' F.univ f := by
  first | exact @GlobalTheory.SiegSpread.classified_basicOpen | exact GlobalTheory.SiegSpread.classified_basicOpen | (intros; apply GlobalTheory.SiegSpread.classified_basicOpen <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelObjectRigidityIdentificationsEq
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

namespace GlobalTheory.SiegRigidCyc

open GlobalTheory.CechPic GlobalTheory.AmpleRigid GlobalTheory.SiegRigid

theorem eq_of_pullback : ∀ (h M : ℕ), 3 ≤ M → ∀ (S S' : Scheme.{0}) (s : S ⟶ Sp (cycAway M)) (s' : S' ⟶ Sp (cycAway M)) (c : SiegPre h M (zetaAway M) s) (o : SiegPre h M (zetaAway M) s') (f : S' ⟶ S), Out.RelAmple c.A c.diag → ∀ (φ ψ : o.A.left ⟶ c.A.left) (φ₂ ψ₂ : (G2 o.A).left ⟶ (G2 c.A).left), IsGrpPullback o.A c.A f φ → IsSquare φ φ₂ → LBIso o.P (c.P.pull φ₂) → (∀ a, (o.lev a).left ≫ φ = f ≫ (c.lev a).left) → IsGrpPullback o.A c.A f ψ → IsSquare ψ ψ₂ → LBIso o.P (c.P.pull ψ₂) → (∀ a, (o.lev a).left ≫ ψ = f ≫ (c.lev a).left) → φ = ψ := by
  intro h M hM S S' s s' c o f hamp φ ψ φ₂ ψ₂ g q w l g' q' w' l'
  obtain ⟨σ, hσ, e⟩ := exists_aut g g'
  have hMu : IsUnit ((M : ℕ) : cycAway M) := isUnit_natCast (show M ≠ 0 by omega)
  have key : σ.hom = 𝟙 _ := by
    refine eq_id_of_forall_geometric_fibre laws_without_cohomology.1 o.A o.ab σ.hom (IsMonHom.one_hom σ.hom)
      fun t => ?_
    let K : Type := AlgebraicClosure (S'.residueField t)
    let j : Sp K ⟶ S' := Spec.map (CommRingCat.ofHom (algebraMap (S'.residueField t) K)) ≫ S'.fromSpecResidueField t
    have hp := isGrpPullback_pullback o.A j
    have := o.ab.smooth
    have := o.ab.proper
    have := o.ab.geomConnected
    have hab : IsAbelianScheme ((Over.pullback j).obj o.A) :=
      { comm := Functor.isCommMonObj_obj
        smooth := by change Smooth (pullback.snd o.A.hom j); infer_instance
        proper := by change IsProper (pullback.snd o.A.hom j); infer_instance
        geomConnected := by change GeometricallyConnected (pullback.snd o.A.hom j); infer_instance }
    have hNK : (M : K) ≠ 0 := by
      have hu := hMu.map (Spec.preimage ((j ≫ f) ≫ s)).hom
      rw [map_natCast] at hu
      exact hu.ne_zero
    have e' := eq_of_field (pull_isLB c.isLB _) hamp hab (hp.comp g) (hp.comp g')
      (by rw [pull_comp, pull_comp]; exact congrArg _ ((pull_cls_diag q w).trans (pull_cls_diag q' w').symm)) hM hNK
      fun Ω _ _ x y hy => by
        have hy₁ : pushHom hp (Over.mk x) y ^ M = 1 := by rw [← map_pow, hy, map_one]
        have e₁ := eq_on_torsion (GlobalTheory.LowChart.isUnit_zetaAway M hM) c g _ l l' Ω (x ≫ j) _ hy₁
        rw [← Category.assoc, ← Category.assoc]
        exact e₁
    refine ⟨_, _, j, _, _, (default : PrimeSpectrum K), ?_, hp.1, ?_⟩
    · exact (Scheme.Hom.comp_apply _ _ _).trans (Scheme.fromSpecResidueField_apply t _)
    · apply g'.1.hom_ext
      · rw [Category.assoc, e]
        exact e'
      · rw [Category.assoc, Over.w]
  rw [← e, key, Over.id_left, Category.id_comp]

end GlobalTheory.SiegRigidCyc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelToroidalPolChartsOfSteps5
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

theorem GlobalTheory.SiegJoin.siegelToroidalPolCharts_of_steps5
    (hF : ∀ g n : ℕ, 1 ≤ g → 3 ≤ n → Odd n → Nonempty (SFam g n (zetaAway n))) (hMin : GlobalTheory.SiegJoin.MinSt5)
    (hPoin : GlobalTheory.Poinc.PoinSt) (hChart : GlobalTheory.SiegJoin.ChartSt5) (hDesc : GlobalTheory.SiegJoin.DescSt5) :
    GlobalTheory.Published.SiegelToroidalPolCharts := by
  intro g hg φ hφ hφ' n hn ho
  have hn0 : n ≠ 0 := by omega
  haveI : IsNoetherianRing (cycAway n) := by haveI := (GlobalTheory.SiegelTor.arBase_cycAway n hn0).1; infer_instance
  obtain ⟨F⟩ := hF g n hg hn ho
  obtain ⟨Z, z, i, OZ, hMA⟩ := hMin g hg n hn ho F
  have hMA' := hMA
  obtain ⟨o', _, β, S', s', U, c, π', G', _, e', _, N', ⟨hTh, hZp, hZn, hiz, hid, hOZ, hOZa⟩, -⟩ := hMA'
  obtain ⟨d, J, S, π, j, BD, hd, hJ, hV, hBl, hP, hj, hjd, hji, hjpre, hBD, hVj, k₀, hk₀⟩ :=
    hPoin g hg n hn ho F Z z i hTh OZ hOZ hOZa φ hφ
  haveI := hj
  have hBlow : BlowAt F z i φ d π j BD := ⟨J, hd, hJ, hV, hBl, hP, hjd, hji, hjpre, hBD, hVj⟩
  obtain ⟨hsm, hpre⟩ := hChart g hg φ hφ hφ' n hn ho F Z z i OZ d S π j BD hMA hBlow
  obtain ⟨G, _, e, hGs, hGd, hGe, hGab⟩ :=
    hDesc g hg φ n hn ho F Z z i d S π j BD hBlow hpre
  haveI := hsm
  haveI : Smooth (π ≫ z) := SmoothOfRelativeDimension.smooth (g * (g + 1) / 2) _
  haveI : QuasiSeparated G.hom := by haveI := hGs.separated; infer_instance
  obtain ⟨a, N, ha, hN, hiso⟩ := GlobalTheory.T.hodgeBundle_power_iso_minimalSiegelCompactification g n F Z z i OZ S π j G e hMA
    (fun x => ⟨hBl.1.isDomain_stalk x, hBl.1.isIntegrallyClosed_stalk x⟩) hP hjd hji hGs hGd hGe
  obtain ⟨N'', hN'', hgen, k, hk⟩ := GlobalTheory.T.exists_globallyGenerated_ample_power_toroidalPullback (cycAway n) Z S z π OZ (hodge G g) (GlobalTheory.CechPic.dual BD.lb) a N
    hZp hOZ hOZa (isLB_hodge G g) (GlobalTheory.CechPic.isLB_dual BD.isLB_lb) ha hN hiso ⟨k₀, hk₀⟩
  refine ⟨F, S, π ≫ z, j, hj, G, inferInstance, e, BD, d, N'', hP, hsm, by rw [← Category.assoc, hji, hiz], ?_,
    hGs, hGd, hGe, hGab, hd, ?_, hN'', hgen, k, hk⟩
  · intro x
    exact GlobalTheory.T.mem_closure_moduliFibre_of_monomialPeriodPreChart F (π ≫ z) j φ BD d x (hpre x)
  · intro x
    exact GlobalTheory.T.hasPolarisedChart_of_monomialPreChart_semiAbelianExt F (π ≫ z) j G e φ BD d x hn0 hGs hGd hGe hGab (hpre x)

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmallSectionCountContinuousFromAboveStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.small_section_count_continuous_from_above : GlobalTheory.Published.ArithHilbertSamuel → GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (b : ℕ) (s t : X.functionField), P.Good D b s t → ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop, ∀ᶠ m : ℕ in atTop, P.lc (n * m : ℕ) m 1 ≤ P.lc (n * m : ℕ) 0 1 + ε * ((n : ℝ) * m) ^ (D + 1) := by
  first | exact @GlobalTheory.VolBr.lc_add_A_le | exact GlobalTheory.VolBr.lc_add_A_le | (intros; apply GlobalTheory.VolBr.lc_add_A_le <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothAlgebraLiftsOverSquareZeroThickeningStatement
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothAlgebra_lifts_over_square_zero_thickening : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (B₀ : Type) [CommRing B₀] [Algebra R₀ B₀], Algebra.Smooth R₀ B₀ → ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B) (p : B →+* B₀), SemiHom π p ∧ Function.Surjective p ∧ (∀ b, p b = 0 ↔ b ∈ I.map (algebraMap R B)) ∧ Algebra.Smooth R B := by
  first | exact @GlobalTheory.smooth_lifts_over_sqZero | exact GlobalTheory.smooth_lifts_over_sqZero | (intros; apply GlobalTheory.smooth_lifts_over_sqZero <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothCoefficientFormsClosedUnderOperationsStatement
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_coefficient_forms_closed_under_operations : ∀ (n : ℕ) (v : V n), (∀ γ : Alt n, (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr ((fun _ : V n => γ) x) S) v)) ∧ (∀ (J : Type) (s : Finset J) (α : J → V n → Alt n), (∀ j ∈ s, ∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (α j x) S) v) → (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (∑ j ∈ s, α j x) S) v)) ∧ (∀ (g : V n → ℂ) (α : V n → Alt n), ContDiffAt ℝ ∞ g v → (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (α x) S) v) → (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (g x • α x) S) v)) ∧ (∀ α β : V n → Alt n, (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (α x) S) v) → (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (β x) S) v) → (∀ S, ContDiffAt ℝ ∞ (fun x => (bas n).repr (α x * β x) S) v)) := by
  first | exact @GlobalTheory.ChernCalc.smooth_coeff_closure | exact GlobalTheory.ChernCalc.smooth_coeff_closure | (intros; apply GlobalTheory.ChernCalc.smooth_coeff_closure <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothSncComponentClosureCharZero
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.SncComp

theorem smooth_of_regular_stalk (K : Type) [Field K] [PerfectField K] (Y : Scheme.{0}) (q : Y ⟶ Sp K)
    [LocallyOfFiniteType q] (d : ℕ)
    (h : ∀ y : Y, IsClosed ({y} : Set Y) →
      IsRegularLocalRing (Y.presheaf.stalk y) ∧ ringKrullDim (Y.presheaf.stalk y) = d) :
    SmoothOfRelativeDimension d q := by
  have : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace q
  choose A _ _ j _ pt hj hq using exists_affine_chart_over q
  let 𝒰 : Y.OpenCover := Scheme.Cover.mkOfCovers Y (fun y => Spec (.of (A y))) j (fun y => ⟨y, pt y, hj y⟩)
  have := HasRingHomProperty.instIsZariskiLocalAtSource (P := @SmoothOfRelativeDimension d)
  refine IsZariskiLocalAtSource.of_openCover (P := @SmoothOfRelativeDimension d) 𝒰 fun (y : Y) => ?_
  change SmoothOfRelativeDimension d (j y ≫ q)
  have hft : LocallyOfFiniteType (spMap (algebraMap K (A y))) := by
    have : LocallyOfFiniteType (j y ≫ q) := inferInstance
    rwa [hq y] at this
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at hft
  have : Algebra.FiniteType K (A y) := RingHom.finiteType_algebraMap.mp hft
  rw [hq y]
  refine RegGenSmooth.smooth_of_regular K (A y) d fun m hm => ?_
  let w : Spec (.of (A y)) := (⟨m, inferInstance⟩ : PrimeSpectrum _)
  have hw : IsClosed ({w} : Set (Spec (.of (A y)))) := (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).2 hm
  have hc : IsClosed ({j y w} : Set Y) := by
    have h1 := (j y).isOpenEmbedding.preimage_closedPoints
    have h2 : w ∈ (j y) ⁻¹' closedPoints Y := by rw [h1]; exact hw
    exact h2
  obtain ⟨h1, h2⟩ := h _ hc
  let e := (asIso ((j y).stalkMap w) ≪≫ Spec.stalkIso (.of _) w).commRingCatIsoToRingEquiv
  exact ⟨IsRegularLocalRing.of_ringEquiv e, (ringKrullDim_eq_of_ringEquiv e).symm.trans h2⟩

theorem smooth_component : ∀ (F : Type) [Field F] [CharZero F] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp F) (e : ℕ), IsProjOver p → SmoothOfRelativeDimension (e + 1) p → ∀ (r : ℕ) (z : Fin r → X), (∀ x : X, FinalTheorems.LSncAt X (fun a => (Closeds.closure {z a})) x) → ∀ a, SmoothOfRelativeDimension e (closι (z a) ≫ p) := by
  intro F _ _ X _ p e _ hsm r z hL a
  have : Smooth p := SmoothOfRelativeDimension.smooth (e + 1) p
  have hdim := GlobalTheory.HSCore.VanishNumberField.topologicalKrullDim_eq_of_smooth p (e + 1) hsm
  refine smooth_of_regular_stalk F _ _ e fun y hy => ?_
  let I := Scheme.IdealSheafData.vanishingIdeal (Closeds.closure {z a})
  have hc : IsClosed ({closι (z a) y} : Set X) := by
    simpa using (closι (z a)).isClosedEmbedding.isClosedMap _ hy
  have hd := (ProperCut.ringKrullDim_stalk_eq p hc).trans hdim
  obtain ⟨hreg, n, t, ε, hR, hI⟩ := hL (closι (z a) y)
  have hmem : closι (z a) y ∈ Closeds.closure {z a} := by
    have := Vanishing.ι_mem_support I y
    have h := Scheme.IdealSheafData.coe_support_vanishingIdeal (Closeds.closure {z a})
    exact h.le this
  have hker : RingHom.ker ((closι (z a)).stalkMap y).hom = Ideal.span {t (ε ⟨a, hmem⟩)} :=
    (Vanishing.ker_stalkMap I y).trans (hI ⟨a, hmem⟩)
  have hm : t (ε ⟨a, hmem⟩) ∈ IsLocalRing.maximalIdeal _ := hR.1 ▸ Ideal.subset_span ⟨_, rfl⟩
  obtain ⟨h1, h2⟩ := isRegularLocalRing_quotient_of_not_mem_sq hm ((regular_params_spec t hR.1 hR.2).1 _)
  let φ := (Ideal.quotEquivOfEq hker.symm).trans
    (RingHom.quotientKerEquivOfSurjective ((closι (z a)).stalkMap_surjective y))
  refine ⟨IsRegularLocalRing.of_ringEquiv φ, ?_⟩
  rw [← ringKrullDim_eq_of_ringEquiv φ]
  rw [hd] at h2
  generalize ringKrullDim (X.presheaf.stalk (closι (z a) y) ⧸ Ideal.span {t (ε ⟨a, hmem⟩)}) = u at h2
  induction u using WithBot.recBotCoe with
  | bot => exact absurd h2 (by rw [WithBot.bot_add]; exact WithBot.bot_ne_coe)
  | coe u =>
    induction u using ENat.recTopCoe with
    | top => exact absurd (WithBot.coe_injective h2) (ENat.top_ne_coe _)
    | coe u =>
      have : u + 1 = e + 1 := by exact_mod_cast h2
      exact_mod_cast Nat.succ_injective this

end GlobalTheory.SncComp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothWeightedLineBundleLogSectionNormProperties
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
open scoped ContDiff

set_option autoImplicit false

namespace GlobalTheory.Mix.SecNorm

theorem logSec_basic : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (M : MLine p σ) (s : M.B.Sec), Measurable (M.logSec s) ∧ (∀ y : CxPts p σ, 0 < M.φ.nsq (secVal p σ s) y ↔ y ∈ ptsIn p σ (nonzeroLocus s)) ∧ (∀ y, CInfAt (M.φ.nsq (secVal p σ s)) y) ∧ ∀ (u : CxPts p σ → ℝ) (hu : ∀ y, CInfAt u y), ∀ y ∈ ptsIn p σ (nonzeroLocus s), (M.addFn u hu).logSec s y = M.logSec s y - u y / 2 := by
  intro k _ X p σ M s
  have hpos : ∀ y : CxPts p σ, 0 < M.φ.nsq (secVal p σ s) y ↔ y ∈ ptsIn p σ (nonzeroLocus s) := fun y => by
    rw [← secVal_ne_zero_iff s (mem_pick M.φ.isLB y), Weight.nsq, mul_pos_iff_of_pos_right (Real.exp_pos _),
      sq_pos_iff, norm_ne_zero_iff]
  refine ⟨?_, hpos, fun y => ?_, fun u hu y hy => ?_⟩
  · exact (Real.measurable_log.comp (M.cInf.continuous_nsq s).measurable).div_const 2
  · have hi := mem_pick M.φ.isLB y
    have ho := (isOpen_ptsIn (p := p) (σ := σ) _).mem_nhds hi
    have h1 : CInfAt (fun z => ‖ev p σ (M.B.U (pick M.φ.isLB y)) (s.f _) z‖ ^ 2) y :=
      ⟨_, Unit, inferInstance, fun _ => s.f _, fun v => ‖v ()‖ ^ 2, univ, hi, isOpen_univ, trivial,
        ((contDiff_apply ℝ ℂ ()).norm_sq ℂ).contDiffOn, EventuallyEq.rfl⟩
    refine (h1.comp₂ (M.cInf _ y hi) (G := fun x => x.1 * Real.exp (-x.2))
      (contDiff_fst.mul contDiff_snd.neg.exp)).congr ?_
    exact eventually_of_mem ho fun z hz => M.φ.nsq_eq (secVal_mem s) hz
  · have h := (hpos y).2 hy
    change Real.log ((M.φ.addFn u).nsq (secVal p σ s) y) / 2 = Real.log (M.φ.nsq (secVal p σ s) y) / 2 - u y / 2
    rw [Weight.nsq_addFn, Real.log_mul h.ne' (Real.exp_pos _).ne', Real.log_exp]
    ring

end GlobalTheory.Mix.SecNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothWeightsDifferBySmoothFunction
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix

namespace GlobalTheory.Mix

theorem weight_sub_cInf : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) (p : X ⟶ Sp k) (σ : k →+* ℂ) (B : LB X) (φ ψ : Weight p σ B), φ.IsCInf → ψ.IsCInf → ∃ u : CxPts p σ → ℝ, (∀ y, CInfAt u y) ∧ ∀ i, ∀ y ∈ ptsIn p σ (B.U i), ψ.φ i y = φ.φ i y + u y := by
  intro k _ X p σ B φ ψ hφ hψ
  have key : ∀ i y, y ∈ ptsIn p σ (B.U i) →
      ψ.φ i y - φ.φ i y = ψ.φ (pick φ.isLB y) y - φ.φ (pick φ.isLB y) y := by
    intro i y hi
    rw [ψ.trans _ i y (mem_pick φ.isLB y) hi, φ.trans _ i y (mem_pick φ.isLB y) hi]
    ring
  refine ⟨fun y => ψ.φ (pick φ.isLB y) y - φ.φ (pick φ.isLB y) y, fun y => ?_, fun i y hi => ?_⟩
  · have hy := mem_pick φ.isLB y
    have hs : CInfAt (fun z => ψ.φ (pick φ.isLB y) z + -φ.φ (pick φ.isLB y) z) y :=
      (hψ _ y hy).add (hφ _ y hy).neg
    refine hs.congr ?_
    filter_upwards [(isOpen_ptsIn _).mem_nhds hy] with z hz
    rw [← key _ z hz, sub_eq_add_neg]
  · have := key i y hi
    linarith

end GlobalTheory.Mix
end

