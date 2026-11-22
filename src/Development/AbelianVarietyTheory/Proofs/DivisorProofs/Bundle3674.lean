import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0004
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1765
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.AuxiliaryPrimeNeTypePrime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1826
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3665
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3672
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3671
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2264
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3647
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3646
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3658
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3122
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3643
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3642
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3645
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3656
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3659
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3072
import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0073
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0089
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3629
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3389
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3626
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AdmissibleBaseChartRing
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0080
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3448
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2344
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3570

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStageTrianglePolynomial
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

namespace GlobalTheory.StageSmall

theorem small_stage : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  GBig fun {D} T _ _ G μ₀ _ _ _ => ∀ (W : G.Weil) (S : GridChoice W Set.univ), IsStdChar D W.ψ (-1) →
    NumbersIn D.what₂.embLL S μ₀ → ∀ (i j : Fin D.R.m) (p q : ℕ) (A A' WW : HSp D) (X : Tri T A A' WW), GlobalTheory.SqTower.IsStageC W i j p q X →
      ∃ P' : PolF D WW.rank A'.rank, (∀ t h, MeasureTheory.IntegrableOn (X.ker' W.ψ W.θ t P' h) X.fd' X.m') ∧ ∀ t, X.I' W.ψ W.θ t P' ≠ 0 := by
  intro hP hK hL
  obtain ⟨c, hc⟩ := GlobalTheory.SqTop.Model.gBig_and (GlobalTheory.T.stage_small_nonzero_base hP hK hL) (GlobalTheory.T.stage_kernel_integrable_polynomial_bound hP hK hL)
  refine ⟨c, fun ε CF hCF => ?_⟩
  obtain ⟨C0, x0, h⟩ := hc ε CF hCF
  refine ⟨C0, x0, fun C hC D large₂ a b r T Lc μ hL G W S hW hN i j p q A A' WW X hX => ?_⟩
  obtain ⟨h1, h2⟩ := h C hC D large₂ a b r T Lc μ hL G
  rcases Nat.eq_zero_or_pos q with rfl | hq
  · have hi := GlobalTheory.T.integrableOn_thetaKernel_definiteSeesawStage G W i j p A A' WW X hX
    obtain ⟨P', hP'⟩ := h1 W S hW hN i j p A A' WW X hX hi
    exact ⟨P', fun t h => hi t P' h, hP'⟩
  · exact h2 W S hW hN i j p q A A' WW X hX hq

end GlobalTheory.StageSmall

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTateModuleIso
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tate_module_iso : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (x : Sp k ⟶ S) (β : R →+* k), x ≫ s = spMap β → ∃ I : GTateIso D.toG k (Over.mk x ⟶ o.A) (fun c g => g ≫ o.act.act c) (fun n g g' z => Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z)), ∀ y, toUnit _ ≫ o.eta y = I.ev N y := by
  first | (exact @GlobalTheory.gen_level_extends_tate) | (exact GlobalTheory.gen_level_extends_tate) | (intros; apply GlobalTheory.gen_level_extends_tate <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorExistsIsotropicStableSummandStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_exists_isotropic_stable_summand : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (tR : R →+* C) (o₀ : GlobalTheory.UPel.HT.Obj b N (spMap π ≫ spMap tR)), ∃ E : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A), (∃ M : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A), IsCompl E M) ∧ (∀ y : HdR o₀.A, y ∈ Fil o₀.A ↔ ∃ d ∈ E, (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ hsq) rfl o₀.A).Corr d y) ∧ (∀ (c : D.O), ∀ d ∈ E, (haveI := o₀.act.hom (c); push (divided₂ hsq) (spMap π) (o₀.act.act (c)) (d)) ∈ E) ∧ (∀ φ : Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] C, GlobalTheory.AbDual.IsCorrForm (divided₂ hsq) (spMap π) o₀.A o₀.A o₀.P φ → ∀ x ∈ E, ∀ y ∈ E, φ x y = 0) ∧ (∀ d : Crys (divided₂ hsq) (spMap π) o₀.A, (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O D.ω); push (divided₂ hsq) (spMap π) (o₀.act.act (algebraMap (𝓞 D.F) D.O D.ω)) (d)) - tR b.ρ • d ∈ E → ∃ w : Fin D.a → Crys (divided₂ hsq) (spMap π) o₀.A, (∀ i (c : 𝓞 D.F), (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O c); push (divided₂ hsq) (spMap π) (o₀.act.act (algebraMap (𝓞 D.F) D.O c)) (w i)) - tR (b.t i c) • w i ∈ E) ∧ d - ∑ i, w i ∈ E) := by
  first | exact @GlobalTheory.HTSummand.exists_summand | exact GlobalTheory.HTSummand.exists_summand | (intros; apply GlobalTheory.HTSummand.exists_summand <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorExistsSquareZeroLiftOfFiltration
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.UPel.HT

theorem exists_sqZero_lift_of_fil : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), N.Coprime p → ∀ (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (tR : R →+* C) (t : Sp C ⟶ Sp R) (t₀ : Sp C₀ ⟶ Sp R), t = spMap tR → t₀ = spMap π ≫ t → ∀ (o₀ : GlobalTheory.UPel.HT.Obj b N t₀) (E : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A)), (∃ M : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A), IsCompl E M) → (∀ y : HdR o₀.A, y ∈ Fil o₀.A ↔ ∃ e ∈ E, (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ hsq) rfl o₀.A).Corr e y) → (∀ (c : D.O), ∀ e ∈ E, (haveI := o₀.act.hom (c); push (divided₂ hsq) (spMap π) (o₀.act.act (c)) (e)) ∈ E) → (∀ Φ : Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] Crys (divided₂ hsq) (spMap π) o₀.A →ₗ[C] C, GlobalTheory.AbDual.IsCorrForm (divided₂ hsq) (spMap π) o₀.A o₀.A o₀.P Φ → ∀ x ∈ E, ∀ y ∈ E, Φ x y = 0) → (∀ e : Crys (divided₂ hsq) (spMap π) o₀.A, (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O D.ω); push (divided₂ hsq) (spMap π) (o₀.act.act (algebraMap (𝓞 D.F) D.O D.ω)) (e)) - tR b.ρ • e ∈ E → ∃ w : Fin D.a → Crys (divided₂ hsq) (spMap π) o₀.A, (∀ i (c : 𝓞 D.F), (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O c); push (divided₂ hsq) (spMap π) (o₀.act.act (algebraMap (𝓞 D.F) D.O c)) (w i)) - tR (b.t i c) • w i ∈ E) ∧ e - ∑ i, w i ∈ E) → ∃ (o : GlobalTheory.UPel.HT.Obj b N t) (m : GlobalTheory.UPel.HT.ObjMap o₀ o (spMap π)), liftFil (divided₂ hsq) m.cart = E := by
  intro p _ D R _ b N hN C C₀ _ _ _ _ π hπ hsq tR t t₀ ht ht₀
  subst ht₀
  subst ht
  intro o₀ E hEc hEf hEs hEi hEl
  obtain ⟨A, _, i, h, act, hA, hE, hact⟩ := GlobalTheory.T.harrisTaylor_exists_lift_orderAction_hodge_summand p D R b N C C₀ π hπ hsq tR o₀ E hEc hEf hEs
  haveI : IsCommMonObj A := hA.comm
  subst hE
  obtain ⟨P, φ₂, hP, r1, r2, hsym, hamp, hker, hros, hsq2, hpol⟩ :=
    GlobalTheory.T.harrisTaylor_exists_polarisation_bundle_lift p D R b N C C₀ π hπ hsq tR o₀ A i h hA act hact hEi
  obtain ⟨eta, e1, e2, e3, e4, e5⟩ := GlobalTheory.T.harrisTaylor_primeToP_level_lift_squareZero p D R b N C C₀ π hπ hsq tR o₀ A i h hA act hact hN P φ₂ hP hsq2 hpol
  exact ⟨{ A := A
           ab := hA
           act := act
           P := P
           isLB := hP
           rig₁ := r1
           rig₂ := r2
           symm := hsym
           ample := hamp
           kerP := hker
           rosati := hros
           lie := fun R' _ β x hx v hv => GlobalTheory.T.harrisTaylor_lift_lie_of_hodge_summand_lie p D R b N C C₀ π hπ hsq tR o₀ A i h hA act hact hEl R' β x hx v hv
           lieRank := fun k _ _ x β hx j => GlobalTheory.T.harrisTaylor_lieMultiplicity_squareZeroLift p D R b N C C₀ π hπ hsq tR o₀ A i h act hact k x β hx j
           eta := eta
           eta_add := e1
           eta_lin := e2
           eta_ker := e3
           geom := e4 },
    { φ := i
      φ₂ := φ₂
      cart := h
      sq := hsq2
      act := hact
      pol := hpol
      eta := e5 }, rfl⟩

end GlobalTheory.UPel.HT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorKodairaSpencerDirectionsDim
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

namespace GlobalTheory.HTCount

theorem sub_smul_mul_sub_smul_eq_zero_of_quadratic {k E : Type*} [Field k] [Ring E] [Algebra k E] (X : E) (tr nm : ℤ) (r r' : k)
    (hX : X * X = (tr : E) * X - (nm : E)) (hs : r + r' = tr) (hp : r * r' = nm) :
    (X - r • (1 : E)) * (X - r' • (1 : E)) = 0 := by
  have htr : (tr : E) = algebraMap k E r + algebraMap k E r' := by rw [← map_add, hs, map_intCast]
  have hnm : (nm : E) = algebraMap k E r * algebraMap k E r' := by rw [← map_mul, hp, map_intCast]
  rw [Algebra.smul_def, Algebra.smul_def, _root_.mul_one, _root_.mul_one, sub_mul, mul_sub, mul_sub, hX, htr, hnm,
    ← Algebra.commutes r' X]
  noncomm_ring

end GlobalTheory.HTCount

namespace GlobalTheory.HTCount

theorem ksDim_at_point : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ φ : LinearMap.BilinForm k (HdR o₀.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → KSDim (GlobalTheory.HTCount.crysAct o₀) φ (Fil o₀.A) (GlobalTheory.HTCount.lieZ o₀ β) (D.a * (D.n - 1)) := by
  intro p _ D R _ b N hN hNp k _ _ t o₀ β ht φ hφ
  obtain ⟨hfd, hdim, hskew, hiso⟩ := GlobalTheory.T.harrisTaylor_pairing_skew_hodge_lagrangian p D R b N hN hNp k t o₀ β ht φ hφ
  have hnd := GlobalTheory.T.harrisTaylor_polarisation_pairing_nondegenerate p D R b N hN hNp k t o₀ β ht φ hφ
  have hadj := GlobalTheory.T.harrisTaylor_crystal_action_adjoint p D R b N hN hNp k t o₀ β ht φ hφ
  have hcount := GlobalTheory.T.harrisTaylor_rho_part_deformation_dim p D R b N hN hNp k t o₀ β ht
  haveI := hfd
  have hstab : ∀ a, ∀ x ∈ Fil o₀.A, crysAct o₀ a x ∈ Fil o₀.A := fun a x hx => by
    haveI := o₀.act.hom a
    rw [crysAct_apply]; exact push_mem_Fil _ hx
  have hcomm : ∀ a, crysAct o₀ (algebraMap (𝓞 D.F) D.O D.ω) * crysAct o₀ a = crysAct o₀ a * crysAct o₀ (algebraMap (𝓞 D.F) D.O D.ω) := fun a => by
    rw [← map_mul, ← map_mul, Algebra.commutes]
  have hsurj : Function.Surjective (fun c : D.O => (D.star c).unop) := fun a => ⟨(D.star a).unop, D.star_star a⟩

  have hbar : D.bar D.ω = (D.tr : 𝓞 D.F) - D.ω := by rw [← D.tr_eq]; ring
  have hωsq : D.ω * D.ω = (D.tr : 𝓞 D.F) * D.ω - (D.nm : 𝓞 D.F) := by
    rw [← D.tr_eq, ← D.nm_eq]; ring
  have hw2 : algebraMap (𝓞 D.F) D.O D.ω * algebraMap (𝓞 D.F) D.O D.ω =
      (D.tr : D.O) * algebraMap (𝓞 D.F) D.O D.ω - (D.nm : D.O) := by
    rw [← map_mul, hωsq, map_sub, map_mul, map_intCast, map_intCast]
  have hstw : (D.star (algebraMap (𝓞 D.F) D.O D.ω)).unop = (D.tr : D.O) - algebraMap (𝓞 D.F) D.O D.ω := by
    rw [D.star_F, MulOpposite.unop_op, hbar, map_sub, map_intCast]
  have hrr : β b.ρ * ((D.tr : k) - β b.ρ) = (D.nm : k) := by
    have := congrArg β b.ρ_root
    simp only [map_add, map_sub, map_mul, map_pow, map_intCast, map_zero] at this
    linear_combination -this
  have hsum : β b.ρ + ((D.tr : k) - β b.ρ) = (D.tr : k) := by ring
  have hdisc : ((D.tr ^ 2 - 4 * D.nm : ℤ) : k) ≠ 0 := by
    have hp : p.Prime := Fact.out
    have hnd : ¬ p ∣ (D.tr ^ 2 - 4 * D.nm).natAbs := fun h => D.disc_p (Int.ofNat_dvd_left.2 h)
    have hcop : (D.tr ^ 2 - 4 * D.nm).natAbs.Coprime p :=
      Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hp).2 hnd)
    have hu := (b.unit _ hcop).map β
    rw [map_natCast] at hu
    intro h0
    rcases Int.natAbs_eq (D.tr ^ 2 - 4 * D.nm) with e | e
    · rw [e, Int.cast_natCast] at h0; exact hu.ne_zero h0
    · rw [e, Int.cast_neg, Int.cast_natCast, neg_eq_zero] at h0; exact hu.ne_zero h0
  have hne : β b.ρ ≠ (D.tr : k) - β b.ρ := by
    intro h
    apply hdisc
    push_cast
    linear_combination (2 * β b.ρ - (D.tr : k)) * h + 4 * hrr
  have hZ : lieZ o₀ β ≤ LinearMap.range (crysAct o₀ (algebraMap (𝓞 D.F) D.O D.ω) - ((D.tr : k) - β b.ρ) • 1) := by
    refine Submodule.span_le.2 ?_
    rintro z ⟨n, lam, c, y, ⟨y₀, rfl⟩, -, rfl⟩
    refine Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ ⟨crysAct o₀ (algebraMap (𝓞 D.F) D.O (c l)) y₀, ?_⟩
    rw [← Module.End.mul_apply, ← Module.End.mul_apply]
    congr 1
    rw [sub_mul, mul_sub, hcomm, smul_mul_assoc, mul_smul_comm, _root_.one_mul, _root_.mul_one]
  generalize lieZ o₀ β = Z at hZ hcount ⊢
  generalize crysAct o₀ = ρ at hstab hcomm hadj hcount hZ ⊢
  generalize algebraMap (𝓞 D.F) D.O D.ω = w at hw2 hstw hcomm hcount hZ
  have hq := sub_smul_mul_sub_smul_eq_zero_of_quadratic (ρ w) D.tr D.nm (β b.ρ) ((D.tr : k) - β b.ρ)
    (by rw [← map_mul, hw2, map_sub, map_mul, map_intCast, map_intCast]) hsum hrr
  have hwadj : ∀ x y, φ (ρ w x) y = φ x ((β b.ρ + ((D.tr : k) - β b.ρ)) • y - ρ w y) := fun x y => by
    rw [hadj, hstw, map_sub, map_intCast, hsum, LinearMap.sub_apply, Module.End.intCast_apply,
      Int.cast_smul_eq_zsmul]
  exact GlobalTheory.T.kodairaSpencer_skew_dim_semisimple_two_roots k (HdR o₀.A) D.O ρ (fun c => (D.star c).unop) φ (Fil o₀.A) Z w (β b.ρ) ((D.tr : k) - β b.ρ) _ hsurj
    hadj hskew hnd hiso hdim hstab hcomm hq hne hwadj hZ hcount

end GlobalTheory.HTCount
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorRealiseKodairaSpencerDirection
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

noncomputable section

namespace GlobalTheory.HTRealise

set_option maxHeartbeats 4000000 in

theorem realise_core (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R]
    (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (hN : N.Coprime p) (k : Type) [Field k] (β : R →+* k)
    (s : Sp k ⟶ Sp R) (hs : s = spMap β) (o₀ : GlobalTheory.UPel.HT.Obj b N s)
    (φ : LinearMap.BilinForm k (HdR o₀.A)) (hφ : GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ)
    (f : HdR o₀.A →ₗ[k] HdR o₀.A)
    (hf : IsKS (GlobalTheory.HTCount.crysAct o₀) φ (Fil o₀.A) (GlobalTheory.HTCount.lieZ o₀ β) f)
    (tR : R →+* DualNumber k) (htR : tR = (algebraMap k (DualNumber k)).comp β)
    (hs' : s = spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ spMap tR) :
    ∃ (o' : GlobalTheory.UPel.HT.Obj b N (spMap tR))
      (m' : GlobalTheory.UPel.HT.ObjMap o₀ o' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)),
      ∀ x ∈ Fil o₀.A, IsFilLift m'.cart x (f x) := by
  have hZ := GlobalTheory.T.lieConditionHodgeSubspace_le_hodgeFiltration p D R b N k β s hs o₀
  subst hs'
  haveI : Module.Finite k (DualNumber k) := inferInstanceAs (Module.Finite k (k × k))
  haveI : IsArtinianRing (DualNumber k) := IsArtinianRing.of_finite k (DualNumber k)
  have hπ : Function.Surjective (TrivSqZeroExt.fstHom k k k).toRingHom :=
    fun r => ⟨TrivSqZeroExt.inl r, rfl⟩
  have hsq : RingHom.ker (TrivSqZeroExt.fstHom k k k).toRingHom ^ 2 = 0 := (SqExt.dual k).sq
  have hA₀ := o₀.ab
  obtain ⟨M, hM⟩ := GlobalTheory.T.dualNumberGraphFiltration_exists_isCompl k o₀.A hA₀ f
  obtain ⟨A, _, i, h, act, hA, hE, hact⟩ := GlobalTheory.HTDeform.exists_lift_oAct p D R b N (DualNumber k) k
    (TrivSqZeroExt.fstHom k k k).toRingHom hπ hsq tR o₀ (graphFil o₀.A f) ⟨M, hM⟩
    (fun y => GlobalTheory.T.mem_hodgeFiltration_iff_dualNumberGraph_reduction k o₀.A hA₀ f y)
    (fun c d hd => by
      haveI := o₀.act.hom c
      exact GlobalTheory.T.dualNumberGraphFiltration_pushforward_mem k o₀.A (o₀.act.act c) f (fun x hx => hf.1 c x hx) d hd)
  haveI : IsCommMonObj A := hA.comm
  obtain ⟨P, φ₂, hP, r1, r2, hsym, hamp, hker, hros, hsq2, hpol⟩ :=
    GlobalTheory.T.harrisTaylor_exists_polarisation_bundle_lift p D R b N (DualNumber k) k (TrivSqZeroExt.fstHom k k k).toRingHom hπ hsq tR o₀ A i h hA act hact
      (fun φ' hφ' x hx y hy => by
        rw [hE] at hx hy
        exact GlobalTheory.T.dualNumberGraphFiltration_isotropic_of_skew k o₀.A hA₀ o₀.P o₀.isLB φ hφ f hf.2.2 φ' hφ' x hx y hy)
  obtain ⟨eta, e1, e2, e3, e4, e5⟩ := GlobalTheory.T.harrisTaylor_primeToP_level_lift_squareZero p D R b N (DualNumber k) k
    (TrivSqZeroExt.fstHom k k k).toRingHom hπ hsq tR o₀ A i h hA act hact hN P φ₂ hP hsq2 hpol
  have hEl : ∀ d : Crys (divided₂ hsq) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) o₀.A,
      (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O D.ω);
        push (divided₂ hsq) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) (o₀.act.act (algebraMap (𝓞 D.F) D.O D.ω)) d)
        - tR b.ρ • d ∈ liftFil (divided₂ hsq) h →
      ∃ w : Fin D.a → Crys (divided₂ hsq) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) o₀.A,
        (∀ i (c : 𝓞 D.F), (haveI := o₀.act.hom (algebraMap (𝓞 D.F) D.O c);
          push (divided₂ hsq) (spMap (TrivSqZeroExt.fstHom k k k).toRingHom) (o₀.act.act (algebraMap (𝓞 D.F) D.O c)) (w i))
            - tR (b.t i c) • w i ∈ liftFil (divided₂ hsq) h) ∧ d - ∑ i, w i ∈ liftFil (divided₂ hsq) h := by
    intro d hd
    rw [hE] at hd ⊢
    subst htR
    exact GlobalTheory.T.dualNumberGraphFiltration_lie_of_map_into_hodge p D R b N k β _ o₀ f hZ hf.2.1 d hd
  refine ⟨{ A := A
            ab := hA
            act := act
            P := P
            isLB := hP
            rig₁ := r1
            rig₂ := r2
            symm := hsym
            ample := hamp
            kerP := hker
            rosati := hros
            lie := fun R' _ β' x hx v hv => GlobalTheory.T.harrisTaylor_lift_lie_of_hodge_summand_lie p D R b N (DualNumber k) k
              (TrivSqZeroExt.fstHom k k k).toRingHom hπ hsq tR o₀ A i h hA act hact hEl R' β' x hx v hv
            lieRank := fun k' _ _ x β' hx j => GlobalTheory.HTLiftLie.lieMult_of_sqZeroLift p D R b N (DualNumber k) k
              (TrivSqZeroExt.fstHom k k k).toRingHom hπ hsq tR o₀ A i h act hact k' x β' hx j
            eta := eta
            eta_add := e1
            eta_lin := e2
            eta_ker := e3
            geom := e4 },
    { φ := i
      φ₂ := φ₂
      cart := h
      sq := hsq2
      act := hact
      pol := hpol
      eta := e5 }, fun x hx => ?_⟩
  obtain ⟨d, hd⟩ := exists_crys hA₀ x (f x)
  refine ⟨d, ?_, hd⟩
  change d ∈ liftFil (divided₂ hsq) h
  rw [hE]
  exact ⟨x, hx, 0, zero_mem _, fun c => by rw [hd c, LinearMap.zero_apply, add_zero]⟩

end GlobalTheory.HTRealise

theorem GlobalTheory.UPel.HT.realise_isKS : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ φ : LinearMap.BilinForm k (HdR o₀.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → ∀ f : HdR o₀.A →ₗ[k] HdR o₀.A, IsKS (GlobalTheory.HTCount.crysAct o₀) φ (Fil o₀.A) (GlobalTheory.HTCount.lieZ o₀ β) f → ∃ (o' : GlobalTheory.UPel.HT.Obj b N (spMap (algebraMap k (DualNumber k)) ≫ t)) (m' : GlobalTheory.UPel.HT.ObjMap o₀ o' (spMap (TrivSqZeroExt.fstHom k k k).toRingHom)), ∀ x ∈ Fil o₀.A, IsFilLift m'.cart x (f x) := by
  intro p _ D R _ b N _ hN k _ _ t o₀ β ht φ hφ f hf
  have e1 : spMap (algebraMap k (DualNumber k)) ≫ t = spMap ((algebraMap k (DualNumber k)).comp β) := by
    rw [ht, ← GlobalTheory.Cris.spMap_comp]
  have e2 : t = spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ spMap ((algebraMap k (DualNumber k)).comp β) := by
    rw [ht, ← GlobalTheory.Cris.spMap_comp]
    exact congrArg spMap (RingHom.ext fun r => rfl)
  rw [e1]
  exact GlobalTheory.HTRealise.realise_core p D R b N hN k β t ht o₀ φ hφ f hf _ rfl e2
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdempotentImageUniformisedByFactorDataStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.idempotent_image_uniformised_by_factor_data : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre), F.Alg → ∀ (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∃ (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G), LBIso (abelian₂ G U.LG.L) ((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left) := by
  first | exact @GlobalTheory.MumDesc.image_unif | exact GlobalTheory.MumDesc.image_unif | (intros; apply GlobalTheory.MumDesc.image_unif <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConstAlongOfKodairaSpencerZeroChart
section
set_option autoImplicit false

noncomputable section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KSConst

theorem isConstAlong_of_ks_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → ∀ (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(Sp (ChartRing k m d), ⊤)) ⟶ t.G.left)), (∀ i, IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) (v i)) → (∀ w, IsTanAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) w → ∃! cf : Fin n → Γ(Sp (ChartRing k m d), ⊤), IsCombAtG t (chart (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens)) v cf w) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ Θ, IsKS t ((Sp (ChartRing k m d)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (∏ i, bdParam k m d i))) (⟨⊤, isAffineOpen_top _⟩ : (Sp (ChartRing k m d)).affineOpens) v (fun r => (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).inv.hom (D ((Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom r))) Θ → (∀ a b, (Scheme.ΓSpecIso (CommRingCat.of (ChartRing k m d))).hom.hom (Θ a b) ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r))) → ∃ c : ℚ, c ≠ 0 ∧ IsConstAlong P.D.toPre (bdParam k m d) gam ρ (fun i => (c : k) * MvPowerSeries.constantCoeff (q i)) := by
  intro E _ _ _ H k _ _ m d t P gam hmon hli hab n v hv hb D q hq Θ hKS hΘ ρ hρ
  have hA := GlobalTheory.MumfordChart.admissibleBase_chartRing k m d
  haveI : IsNoetherianRing (ChartRing k m d) := hA.1
  haveI : IsAdicComplete (maximalIdeal (ChartRing k m d)) (ChartRing k m d) := hA.2.2.2
  letI := H.starRing
  obtain ⟨Y⟩ : Nonempty (Ray P.oD) := inferInstance
  obtain ⟨n', v', dd, hdd⟩ := GlobalTheory.T.exists_basis_raynaudTangent_invariantFields (ChartRing k m d) P.D.toPre (𝓞 E) P.oD Y
  have hne : ∀ i, bdParam k m d i ≠ 0 := fun i h0 => by
    have h4 := congrArg (fun f : ChartRing k m d => MvPowerSeries.coeff (Finsupp.single (Sum.inl i) 1) f) h0
    simp [bdParam, MvPowerSeries.coeff_X] at h4
  have f1 : ∀ x y, D (x + y) = D x + D y := D.map_add
  have f2 : ∀ (z : ℤ) (x : ChartRing k m d), D (z • x) = z • D x := fun z x => map_zsmul D z x
  have f3 : D 1 = 0 := D.map_one_eq_zero
  have f4 : ∀ x y, D (x * y) = x • D y + y • D x := D.leibniz
  obtain ⟨h, hB, hD⟩ : ∃ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h ∧ HasDefect Y h (fun _ _ _ => 0) := by
    generalize (⇑D : ChartRing k m d → ChartRing k m d) = f at f1 f2 f3 f4 hq ⊢
    letI : Algebra ℤ (ChartRing k m d) := Ring.toIntAlgebra _
    let D' : Derivation ℤ (ChartRing k m d) (ChartRing k m d) :=
      { toFun := f, map_add' := f1, map_smul' := fun z x => f2 z x, map_one_eq_zero' := f3, leibniz' := f4 }
    exact GlobalTheory.T.exists_torusInvariant_heatOperator_commuting_periods (ChartRing k m d) P.D (𝓞 E) P.oD Y n' v' dd hdd m (bdParam k m d) gam hmon hne D'
      (fun i => by
        show f (bdParam k m d i) ∈ _
        rw [hq i]; exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _))
  exact GlobalTheory.T.degenerationData_constant_of_flat_heatOperators E H k m d t P gam hmon hli hab Y n' v' dd hdd D q hq h hB hD
    (GlobalTheory.T.heat_symbol_mem_maximalIdeal_of_kodairaSpencer_zero E H k m d t P gam hmon hli hab n v hv hb Y n' v' dd hdd D q hq h hB hD Θ hKS hΘ) ρ hρ
end GlobalTheory.KSConst
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryCompactificationExistsBoundaryIdeal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc
open GlobalTheory
open Classical

namespace GlobalTheory.UPoinc

theorem uIdealSt_holds : UIdealSt := by
  intro E _ _ _ H Dw hpq φ hφ l Xo c C
  haveI : IsNoetherianRing C.o := C.ded.toIsDedekindRing.toIsNoetherian
  haveI : AlgebraicGeometry.IsNoetherian C.Z := GlobalTheory.isNoetherian_of_isProjOver C.proj
  have hdom : ∀ x : C.Z, IsDomain (C.Z.presheaf.stalk x) := fun x => C.normal.isDomain_stalk x
  have hfin : (irreducibleComponents C.Z).Finite := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
  letI : Fintype (irreducibleComponents C.Z) := hfin.fintype
  have hclo : ∀ k : irreducibleComponents C.Z, IsClopen (k : Set C.Z) := fun k =>
    ⟨isClosed_of_mem_irreducibleComponents _ k.2, GlobalTheory.CompPart.isOpen_of_mem hdom k.2⟩
  have key : ∀ k : irreducibleComponents C.Z, ∃ (d : ℕ) (J : C.Z.IdealSheafData), 1 ≤ d ∧
      (∀ x ∈ J.support, x ∈ (k : Set C.Z) ∧ x ∉ Set.range C.i) ∧ UValThru Xo c C.i (𝟙 C.Z) k φ J d := by
    intro k
    by_cases hk : ((k : Set C.Z) ∩ Set.range C.i).Nonempty
    · obtain ⟨X₁, ι, J₁, h1, h2, h3, h4⟩ := GlobalTheory.T.exists_unitaryThetaSetup_ideal_over_component E H Dw hpq φ hφ l Xo c C k (hclo k) k.2.1 hk
      exact GlobalTheory.T.ideal_descent_to_component_compactification E H Dw hpq φ hφ l Xo c C k (hclo k) k.2.1 hk X₁ ι J₁ h1 h2 h3 h4
    · refine ⟨1, ⊤, le_rfl, fun x hx => ?_, uValThru_top_of_disjoint (hclo k).2 (Set.not_nonempty_iff_eq_empty.1 hk) φ 1⟩
      rw [Scheme.IdealSheafData.support_top] at hx
      exact absurd hx (by simp [← SetLike.mem_coe])
  choose d J hd hJ hv using key
  exact exists_uValOn_of_pieces (ι := irreducibleComponents C.Z) C.i φ (fun k => (k : Set C.Z)) J d (GlobalTheory.CompPart.existsUnique_mem hdom) hd hJ hv

end GlobalTheory.UPoinc
end

