import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0417
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3261
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0577
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0705
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0029
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0010
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0009
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2513
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2670
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0587
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2868
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2834
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3256
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3168
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3176
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHolPeriods
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3104
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3220
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3164
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0908
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0086
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3221
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3125
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3161
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3233
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3229
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3120
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3119
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3133
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3237
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3177
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3162
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0085
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3047
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3218
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3200
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerThetaCoefficientEqConstMulMonomial
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0075
import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3257
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0076
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0672
import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3258
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RigExtMapRelFrobCompRigOfOmega
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3070
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3132
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0005

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartDimAddFinrankDualLieEqHeight
section
set_option autoImplicit false

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
open TensorProduct

namespace GlobalTheory.PDivGroup.DimSum

theorem baseChange_bijective_of_ker {O : Type} [CommRing O] {M N : Type} [AddCommGroup M] [Module O M]
    [AddCommGroup N] [Module O N] (k : Type) [CommRing k] [Algebra O k] (a : O)
    (ha : algebraMap O k a = 0) (f : M →ₗ[O] N) (hf : Function.Surjective f)
    (hfa : ∀ v, f (a • v) = 0) (hk : ∀ w, f w = 0 → ∃ v, w = a • v) :
    Function.Bijective (f.baseChange k) := by
  rw [LinearMap.baseChange_eq_ltensor]
  refine ⟨?_, LinearMap.lTensor_surjective k hf⟩
  have hex : Function.Exact (a • LinearMap.id : M →ₗ[O] M) f := by
    intro w
    constructor
    · intro hw
      obtain ⟨v, rfl⟩ := hk w hw
      exact ⟨v, rfl⟩
    · rintro ⟨v, rfl⟩
      exact hfa v
  have hex' := lTensor_exact k hex hf
  have hz : LinearMap.lTensor k (a • LinearMap.id : M →ₗ[O] M) = 0 := by
    refine TensorProduct.ext' fun c m => ?_
    rw [LinearMap.lTensor_tmul, LinearMap.smul_apply, LinearMap.id_apply, ← TensorProduct.smul_tmul,
      Algebra.smul_def, ha, zero_mul, TensorProduct.zero_tmul, LinearMap.zero_apply]
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, rfl⟩ := (hex' x).1 hx
  rw [hz, LinearMap.zero_apply]

open GlobalTheory.PDiv Module

theorem finrank_cot_baseChange_one {p : ℕ} {O : Type} [CommRing O] (H : PDivGroup p O) (k : Type)
    [Field k] [Algebra O k] (hp : algebraMap O k p = 0) :
    finrank k (Cot k (k ⊗[O] H.A 1)) = finrank k (k ⊗[O] H.omega) := by
  have h1 : Function.Bijective ((H.omegaLevel 1).baseChange k) :=
    baseChange_bijective_of_ker k (p : O) hp (H.omegaLevel 1) (H.omegaLevel_surjective 1)
      (fun v => by
        have := H.pow_smul_cot 1 (v.1 1)
        rw [pow_one] at this
        exact this)
      (fun w hw => by
        obtain ⟨v, hv⟩ := (H.omega_val_eq_zero_iff 1 w).1 hw
        exact ⟨v, by rw [hv, pow_one]⟩)
  let e1 := LinearEquiv.ofBijective _ h1
  let e2 := LinearEquiv.ofBijective _ (liftSemi_toBaseChange_cot_bijective O k (H.A 1))
  exact (e1.trans e2).finrank_eq.symm

theorem finrank_cot_congr {k X Y : Type} [Field k] [CommRing X] [CommRing Y] [Bialgebra k X]
    [Bialgebra k Y] (e : X ≃ₐc[k] Y) : finrank k (Cot k X) = finrank k (Cot k Y) := by
  have h1 : (e.symm : Y →ₐc[k] X).comp (e : X →ₐc[k] Y) = BialgHom.id k X :=
    BialgHom.ext fun x => e.symm_apply_apply x
  have h2 : (e : X →ₐc[k] Y).comp (e.symm : Y →ₐc[k] X) = BialgHom.id k Y :=
    BialgHom.ext fun x => e.apply_symm_apply x
  refine (LinearEquiv.ofLinear (cotMap (e : X →ₐc[k] Y)) (cotMap (e.symm : Y →ₐc[k] X)) ?_ ?_).finrank_eq
  · rw [← cotMap_comp, h2, cotMap_id]
  · rw [← cotMap_comp, h1, cotMap_id]

end GlobalTheory.PDivGroup.DimSum

open Module PDiv in

theorem GlobalTheory.PDivGroup.chart_dim_add_finrank_dual_lie : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C]
    [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C]
    [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O →
    ∀ (G : PDivGroup p O) (d : ℕ) (c : QLog.Chart G d),
      d + Module.finrank O G.dual.Lie = G.height := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv G d c
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  let k := IsLocalRing.ResidueField O
  have hpk : algebraMap O k p = 0 := by
    change IsLocalRing.residue O p = 0
    rw [IsLocalRing.residue_eq_zero_iff]
    exact (Fact.out : ¬IsUnit (p : O))
  have hpk' : ((p : ℕ) : k) = 0 := by rw [← map_natCast (algebraMap O k), hpk]
  obtain ⟨hbij, -⟩ := GlobalTheory.T.pdDivGroupChart_forms_basis_and_differential p C v O hv G d c
  let eG : (Fin d → O) ≃ₗ[O] G.omega := LinearEquiv.ofBijective _ hbij
  haveI : Module.Free O G.omega := Module.Free.of_equiv eG
  obtain ⟨hfin, hproj⟩ := GlobalTheory.PDiv.omega_finite_projective p C v O hv G.dual
  haveI : Module.Free O G.dual.omega := Module.free_of_flat_of_isLocalRing
  have hd : finrank O G.omega = d := by rw [← eG.finrank_eq, Module.finrank_fin_fun]
  have hLie : finrank O G.dual.Lie = finrank O G.dual.omega := by
    let b := Module.Free.chooseBasis O G.dual.omega
    rw [finrank_eq_card_basis b.dualBasis, finrank_eq_card_basis b]
  obtain ⟨-, -, -, hsum⟩ := finrank_rigExt_omega p k hpk' (G.baseChange k)
  have hA : finrank k (G.baseChange k).omega = finrank O G.omega := by
    rw [(LinearEquiv.ofBijective _ ((G.baseChange k).omegaLevel_one_bijective hpk')).finrank_eq]
    exact (DimSum.finrank_cot_baseChange_one G k hpk).trans (Module.finrank_baseChange)
  have hB : finrank k (G.baseChange k).dual.omega = finrank O G.dual.omega := by
    rw [(LinearEquiv.ofBijective _ ((G.baseChange k).dual.omegaLevel_one_bijective hpk')).finrank_eq]
    refine (DimSum.finrank_cot_congr (CartierDual.baseChange O k (G.A 1))).symm.trans ?_
    exact (DimSum.finrank_cot_baseChange_one G.dual k hpk).trans (Module.finrank_baseChange)
  rw [hLie, ← hd, ← hA, ← hB]
  exact hsum
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmFieldLatticeIntegrality
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LatModel

theorem exists_model_periods : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.SerreTateGoodReductionSt → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal →
  GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.PolarisationModule →
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (I : Type) [Fintype I] (d : ℕ)
    (φ : I → E →+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData d φ → ∀ (𝔣 : Ideal (OF E)) (Λ : PeriodPair), IsBaseCond 𝔣 → GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsIntLattice d Λ →
    ∀ (l : ℕ) [Fact l.Prime] (Q : Finset (HeightOneSpectrum (OF E))), IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) →
    ∀ y : (Af E)ˣ, OneOver l y → ∀ (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (Ω : ℂ), Ω ^ 12 = latDisc Λ →
    ∃ (𝔠 : FracId (FR E)) (R : Subring ℂ) (_ : IsPlaceRing E l lam R) (X₀ : Obj (FR E) 𝔠 (Sp R)) (X : Obj (FR E) 𝔠 (Sp ℂ))
      (U : Unif φ (lattice (condQ 𝔣 Q) y) 0 X) (p : X.A.left ⟶ X₀.A.left) (cm : OAct (orderC (condQ 𝔣 Q)) X₀.A),
      X.IsPullBy X₀ (spMap R.subtype) p ∧
      (∀ a : OF E, cm.act (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF (condQ 𝔣 Q) a) = X₀.rm.act a) ∧
      (∀ a : orderC (condQ 𝔣 Q), ∃ (α : X.A ⟶ X.A) (_ : IsMonHom α), α.left ≫ p = p ≫ (cm.act a).left ∧
        ∀ w, U.u.ex (fun j ↦ φ (U.e j) (a : E) * w j) = U.u.ex w ≫ α) ∧
      ∀ (i : I) (e : X₀.Lie →ₗ[R] R) (a : ℂ), IsPeriodGen X₀ U p i e a → a ≠ 0 → Sz l lam (a0 𝔣 l) (a / Ω) := by
  intro hPer hST hDR hDC hPol E _ _ _ _ I _ d φ hF 𝔣 Λ h𝔣 hΛ l _ Q hQ hQl y hy lam Ω hΩ
  have hc : condQ 𝔣 Q ≠ ⊥ := by
    rw [← Ideal.zero_eq_bot]
    refine mul_ne_zero (by rw [Ideal.zero_eq_bot]; exact h𝔣.1) (Finset.prod_ne_zero_iff.2 fun q _ ↦ ?_)
    rw [Ideal.zero_eq_bot]; exact q.ne_bot
  obtain ⟨𝔠, X, U, hend⟩ := GlobalTheory.T.cm_order_uniformization_exists E I d φ hF (condQ 𝔣 Q) y hc
  obtain ⟨k₀, R₀, hk₀, hR₀, hR₀k, G₀, _, p₀, P₀, Ψ₀, hG₀, hp₀, hΨ₀, hΨf, hΨfl, hΨs, htan⟩ :=
    GlobalTheory.T.integral_lattice_l_adic_congruence hST hDC E I d φ hF 𝔣 Λ h𝔣 hΛ l Q hQ hQl y hy lam Ω hΩ 𝔠 X U
  obtain ⟨k, hk, H⟩ := (GlobalTheory.T.cm_order_l_adic_endomorphism_integral hDC hDR E I φ hF.2.2.2.2.2.2.1 (condQ 𝔣 Q) y hc l lam 𝔠 X U hend k₀ R₀ hk₀ hR₀ hR₀k
    G₀ p₀ P₀ Ψ₀ hG₀ hp₀ hΨ₀ hΨf hΨfl hΨs).and (GlobalTheory.T.eventually_place_ring E l lam)
  obtain ⟨R, hR⟩ := GlobalTheory.T.exists_place_ring_over_prime l lam k hk
  obtain ⟨⟨X₀, p, cm, hpb, hrm, hcm, hlie⟩, hplace⟩ := H R hR
  refine ⟨𝔠, R, hplace, X₀, X, U, p, cm, hpb, hrm, fun a ↦ ?_, fun i e a he _ ↦ ?_⟩
  · obtain ⟨α, hα, hα'⟩ := hend a
    exact ⟨α, hα, hcm a α hα hα', hα'⟩
  · obtain ⟨v₀, v', W, htv, hvv, hW, hW0, hsz⟩ := htan i
    obtain ⟨v, hv⟩ := hlie v₀ v' htv hvv
    exact sz_period_of_tangent hplace he hv hW hW0 hsz

end GlobalTheory.LatModel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexUniformisationOfMarkedPeriodsFamily
section
noncomputable section

namespace GlobalTheory.PELU

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix

theorem isPeriod_comp_isometry_symm {O : Type} [Ring O] {bar : O → O} {g : ℕ} {ρ : O →+* Matrix (Fin g) (Fin g) ℂ}
    (D D' : PLat O bar) (w : D.La ≃ₗ[O] D'.La) (hw : IsIsom D D' w) (P : D.La →+ (Fin g → ℂ))
    (hP : IsPeriod D ρ P) : IsPeriod D' ρ (P.comp w.symm.toLinearMap.toAddMonoidHom) := by
  obtain ⟨hlin, hinj, hdisc, hspan, Hm, hH, hpos, him⟩ := hP
  have hrange : (P.comp w.symm.toLinearMap.toAddMonoidHom).range = P.range := by
    ext v
    simp only [AddMonoidHom.mem_range, AddMonoidHom.comp_apply]
    constructor
    · rintro ⟨x, rfl⟩; exact ⟨_, rfl⟩
    · rintro ⟨x, rfl⟩; exact ⟨w x, by simp⟩
  have hrange' : Set.range (P.comp w.symm.toLinearMap.toAddMonoidHom) = Set.range P := by
    have := congrArg (fun S : AddSubgroup (Fin g → ℂ) => (S : Set (Fin g → ℂ))) hrange
    simpa [AddMonoidHom.coe_range] using this
  refine ⟨fun a x => ?_, ?_, ?_, ?_, Hm, hH, hpos, fun x y => ?_⟩
  · simp [hlin]
  · intro x y hxy
    have := hinj hxy
    simpa using this
  · rw [hrange]; exact hdisc
  · rw [hrange']; exact hspan
  · have := hw (w.symm x) (w.symm y)
    simp only [LinearEquiv.apply_symm_apply] at this
    simp [him, this]

theorem unif_of_fineAt : ∀ (O : Type) [Ring O] (bar : O → O) (g : ℕ) (ρ : O →+* Matrix (Fin g) (Fin g) ℂ) (Λ : Type)
    (F : Fam ℂ O Λ g) (N : ℕ) (C : ∀ D' : PLat O bar, (Λ → D'.La) → Prop) (d : ℕ), 3 ≤ N → (∀ a, F.eta a ^ N = 1) →
    SmoothOfRelativeDimension d F.s → QuasiCompact F.s → (∀ D' t, C D' t → FullMark N D' t) →
    FineAt F (RingHom.id ℂ) ρ N C → Nonempty (Unif F (RingHom.id ℂ) ρ N C) := by
  intro O _ bar g ρ Λ F N C d hN heta hsm hqc hfull hF
  have hN0 : 0 < N := by omega
  have hlft : LocallyOfFiniteType F.s := by
    haveI := hsm
    haveI : Smooth F.s := SmoothOfRelativeDimension.smooth d F.s
    infer_instance
  obtain ⟨n, Di, t, hmem, hall, hdist⟩ := GlobalTheory.T.exists_finite_markedLattice_period_representatives O bar g ρ Λ F N C d hN0 heta hsm hqc hF
  have hQ : ∀ i (P : (Di i).La →+ (Fin g → ℂ)), ∃ Q, IsPeriod (Di i) ρ Q ∧ (IsPeriod (Di i) ρ P → Q = P) := by
    intro i P
    by_cases hP : IsPeriod (Di i) ρ P
    · exact ⟨P, hP, fun _ => rfl⟩
    · obtain ⟨Q, hQ⟩ := (hmem i).2
      exact ⟨Q, hQ, fun h => absurd h hP⟩
  choose Q hQp hQe using hQ
  have hex : ∀ i P, ∃ y e, UnifAt F (RingHom.id ℂ) ρ N (Di i) (t i) (Q i P) y e :=
    fun i P => hF.occ _ _ _ (hmem i).1 (hQp i P)
  choose u ex hu using hex
  have hunif : ∀ i P, IsPeriod (Di i) ρ P → UnifAt F (RingHom.id ℂ) ρ N (Di i) (t i) P (u i P) (ex i P) := by
    intro i P hP
    have := hu i P
    rwa [hQe i P hP] at this
  have hrefl : ∀ i, IsMarkedIsom N (Di i) (Di i) (t i) (t i) (LinearEquiv.refl O _) :=
    fun i => ⟨fun x y => rfl, fun a => ⟨0, by simp⟩⟩
  have cmpEq : ∀ (D' D'' : PLat O bar) (t' : Λ → D'.La) (t'' : Λ → D''.La) (P : D'.La →+ (Fin g → ℂ))
      (P' : D''.La →+ (Fin g → ℂ)) (y y' : Sp ℂ ⟶ F.X) (e : (Fin g → ℂ) → (Over.mk y ⟶ F.A))
      (e' : (Fin g → ℂ) → (Over.mk y' ⟶ F.A)), y = y' →
      UnifAt F (RingHom.id ℂ) ρ N D' t' P y e → UnifAt F (RingHom.id ℂ) ρ N D'' t'' P' y' e' →
      ∃ (w : D'.La ≃ₗ[O] D''.La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)),
        IsMarkedIsom N D' D'' t' t'' w ∧ ∀ x, P' (w x) = h (P x) := by
    intro D' D'' t' t'' P P' y y' e e' hy h1 h2
    subst hy
    obtain ⟨w, h, hw, hP, -⟩ := GlobalTheory.T.complexUniformisations_same_point_differ_by_isometry O bar g ρ ℂ (RingHom.id ℂ) Λ F N D' D'' t' t'' P P' y e e' hN0 h1 h2
    exact ⟨w, h, hw, hP⟩
  refine ⟨{
      n := n
      Di := Di
      t := t
      mem := fun i => (hmem i).1
      ne := fun i => (hmem i).2
      all := hall
      distinct := hdist
      u := u
      ex := ex
      unif := hunif
      onto := ?_
      disj := ?_
      fibre := ?_
      hol := ?_
      lift := ?_ }⟩
  · intro y hy
    obtain ⟨D', t', P, e, hC, hU⟩ := hF.pts y hy
    obtain ⟨i, w, hw⟩ := hall D' t' hC ⟨P, hU.2.1⟩
    have hP' := isPeriod_comp_isometry_symm D' (Di i) w hw.1 P hU.2.1
    refine ⟨i, _, hP', ?_⟩
    exact (hF.sep D' (Di i) t' (t i) P _ y _ e (ex i _) hU (hunif i _ hP') w (LinearEquiv.refl ℂ _) hw
      (fun x => by simp)).symm
  · intro i j P P' hP hP' huu
    obtain ⟨w, h, hw, -⟩ := cmpEq _ _ _ _ _ _ _ _ _ _ huu (hunif i P hP) (hunif j P' hP')
    exact hdist i j w hw
  · intro i P P' hP hP'
    constructor
    · intro huu
      exact cmpEq _ _ _ _ _ _ _ _ _ _ huu (hunif i P hP) (hunif i P' hP')
    · rintro ⟨w, h, hw, hPw⟩
      exact hF.sep _ _ _ _ _ _ _ _ _ _ (hunif i P hP) (hunif i P' hP') w h hw hPw
  · intro i m B P hB hHol
    exact GlobalTheory.T.basePoint_and_exponential_holomorphic_in_periods O bar g ρ Λ F N C d (Di i) (t i) m B P (fun b => u i (P b)) (fun b => ex i (P b)) hN heta hsm
      hqc hF (hmem i).1 (hfull _ _ (hmem i).1) hB hHol (fun b hb => hunif i (P b) (hHol.1 b hb))
  · intro m B y hB hy hhol b₀ hb₀
    obtain ⟨D', t', P, e, hC, hU⟩ := hF.pts (y b₀) (hy b₀ hb₀)
    obtain ⟨i, w, hw⟩ := hall D' t' hC ⟨P, hU.2.1⟩
    have hP' := isPeriod_comp_isometry_symm D' (Di i) w hw.1 P hU.2.1
    have hU' := GlobalTheory.T.uniformisationAt_transport_isometry O bar g ρ ℂ (RingHom.id ℂ) Λ F N D' (Di i) t' (t i) P _ (y b₀) e w
      (LinearEquiv.refl ℂ _) hN0 hU hw (fun x => by simp) hP'
    obtain ⟨B', P₁, e₁, hB', hb₀', hBB, -, hHol, -, hU₁⟩ :=
      GlobalTheory.T.holomorphicMap_lifts_locally_to_periodFamilies O bar g ρ Λ F N (Di i) (t i) m B y b₀ _ _ hN0 heta hlft hB hb₀ hy hhol hU'
    refine ⟨B', i, P₁, hB', hb₀', hBB, hHol, fun b hb => ?_⟩
    exact hF.sep _ _ _ _ _ _ _ _ _ _ (hunif i (P₁ b) (hHol.1 b hb)) (hU₁ b hb) (LinearEquiv.refl O _)
      (LinearEquiv.refl ℂ _) (hrefl i) (fun x => rfl)

end GlobalTheory.PELU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOnDens
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical

namespace GlobalTheory.FlagCell2.LocFib

theorem continuousOn_dens {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n) {α : A.Fld} (hα : A.IsForm α)
    (i : A.ι) : ContinuousOn (fun v => (dens (A.loc α i v)).re) (A.e i).target :=
  Complex.continuous_re.comp_continuousOn ((hα.smooth i Finset.univ).continuousOn.div_const _)

set_option maxHeartbeats 800000 in

theorem part_preimage : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X Y : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ) (E : Fr (ratOf X) m 0) (E' : Fr (ratOf Y) m m) (φ : X.Fn →ₐ[F] Y.Fn) (f : Y.X ⟶ X.X) (hf : f ≫ X.str = Y.str), Refines E E' φ f → ∀ H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ, IsMetricOn E ⊤ H → ∀ α : (atlas X σ).Fld, (atlas X σ).IsForm α → (atlas Y σ).IsForm ((atlas X σ).pullback (atlas Y σ) (ptMap σ f hf) α * evalF (atlas Y σ) (grF E' (pullGram E H φ f hf)) (fibrePoint m)) → ∀ (s : ℤˣ) (c : AlgChart X.str σ X.dim) (A : Mat m X.Fn) (O : Set (CxPts X.str σ)), IsOpen O → O ⊆ c.e.source → (∀ x ∈ O, A ∈ E.S (under x)) → ∀ T, MeasurableSet T → T ⊆ O → (atlas Y σ).part ((atlas X σ).pullback (atlas Y σ) (ptMap σ f hf) α * evalF (atlas Y σ) (grF E' (pullGram E H φ f hf)) (fibrePoint m)) s (ptMap σ f hf ⁻¹' T) = (atlas X σ).part α s T := by
  intro F _ σ X Y ι _ m E E' φ f hf hR H hH α hα hβ s c A O hO hOc hOA T hT hTO
  rcases T.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · simp
  haveI : T2Space (CxPts X.str σ) := CxPts.t2Space _ _
  haveI : T2Space (CxPts Y.str σ) := CxPts.t2Space _ _
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_genericPoint_flag_in_cell_of_frame F X Y ι m E E' φ f hR _ A (hOA x₀ (hTO hx₀))
  have hdim := GlobalTheory.T.flagRefinementBundle_dim_eq_base_add_card_aboveDiagonal F σ X Y ι m E E' φ f hf hR
  let ε : Fin Y.dim ≃ Fin X.dim ⊕ Cell m := Fintype.equivOfCardEq (by simp [hdim])
  obtain ⟨hopen, hinj, himg⟩ := GlobalTheory.T.flagCell_coords_bijective_onto_chart_prod F σ X Y ι m E E' φ f hf hR c A u hu _ ε
  have hW := (GlobalTheory.T.isOpen_flagBundleCell_and_coords_regular F X Y ι m E E' φ f hR A u).1
  have hπ : Continuous (ptMap σ f hf) := GlobalTheory.Points.PtsOver.continuous_map f hf _
  have hTm : MeasurableSet (ptMap σ f hf ⁻¹' T) := hπ.measurable hT
  have hnull := GlobalTheory.T.formPart_compl_complexPointsInOpen_eq_zero F σ Y ((atlas X σ).pullback (atlas Y σ) (ptMap σ f hf) α *
    evalF (atlas Y σ) (grF E' (pullGram E H φ f hf)) (fibrePoint m)) ⟨_, hW⟩ hu s
  obtain ⟨μ, hμ⟩ : ∃ μ, μ = (atlas Y σ).part ((atlas X σ).pullback (atlas Y σ) (ptMap σ f hf) α *
    evalF (atlas Y σ) (grF E' (pullGram E H φ f hf)) (fibrePoint m)) s := ⟨_, rfl⟩
  rw [← hμ] at hnull ⊢
  have h1 : μ (ptMap σ f hf ⁻¹' T) = μ (ptMap σ f hf ⁻¹' T ∩ cellSet E E' φ f hf c A u) := by
    refine (measure_inter_add_diff (ptMap σ f hf ⁻¹' T) hopen.measurableSet).symm.trans ?_
    have h0 : μ (ptMap σ f hf ⁻¹' T \ cellSet E E' φ f hf c A u) = 0 :=
      by
      refine measure_mono_null (fun y hy => ?_) hnull
      intro hy'
      have h2 : under y ∈ (⟨_, hW⟩ : Y.X.Opens) := mem_ptsIn.1 hy'
      have h3 : InCell E E' φ f A u (under y) := h2
      exact hy.2 ⟨h3, hOc (hTO hy.1)⟩
    rw [h0, add_zero]
  have hmet := GlobalTheory.T.flaggedBundleMetric_smoothUnit_etaleChart F σ X ι m 0 E H (isMetricFr_of_isMetricOn hH)
  have hG : ∀ v ∈ c.e '' O, ∀ τ, MContDiffAt ∞ (fun w => H A (c.e.symm w) τ) v ∧ (H A (c.e.symm v) τ).PosDef := by
    rintro _ ⟨x, hx, rfl⟩ τ
    exact ((hmet x A (hOA x hx) τ).2 c (hOc hx)).self_of_nhds
  have hOo : IsOpen (c.e '' O) := c.e.isOpen_image_of_subset_source hO hOc
  have hTi : MeasurableSet (c.e '' T) := by
    have e : c.e '' T = Subtype.val '' (c.e.target.restrict c.e.symm ⁻¹' T) := by
      ext v
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨_, c.e.map_source (hOc (hTO hx))⟩, by
          show c.e.symm (c.e x) ∈ T
          rwa [c.e.left_inv (hOc (hTO hx))], rfl⟩
      · rintro ⟨v, hv, rfl⟩
        exact ⟨_, hv, c.e.right_inv v.2⟩
    rw [e]
    exact (MeasurableEmbedding.subtype_coe c.e.open_target.measurableSet).measurableSet_image.2
      ((continuousOn_iff_continuous_restrict.1 c.e.continuousOn_symm).measurable hT)
  rw [h1, hμ, GlobalTheory.T.formPart_eq_lintegral_image_injective_holomorphic _ _ (atlas Y σ) _ hβ _ (cellMap ε f hf c u)
    (cellForm ε (fun v => H A (c.e.symm v)) ((atlas X σ).loc α c)) hopen hinj ?_ s _
    (hTm.inter hopen.measurableSet) Set.inter_subset_right, himg T (hTO.trans hOc) fun x hx => hOA x (hTO hx),
    show (atlas X σ).part α s T = ∫⁻ v in c.e '' T, ENNReal.ofReal (((s : ℤ) : ℝ) * (dens ((atlas X σ).loc α c v)).re)
      from GlobalTheory.T.formPart_subset_chart_eq_lintegral_image _ _ (atlas X σ) α hα s c T hT (hTO.trans hOc),
    ← GlobalTheory.T.setLIntegral_flagCellFibreDensity_eq_base ι m _ _ ε (fun v => H A (c.e.symm v))
      (fun v => ((s : ℤ) : ℝ) * (dens ((atlas X σ).loc α c v)).re) (c.e '' O) (c.e '' T) hOo hTi (Set.image_mono hTO)
      (continuousOn_const.mul ((continuousOn_dens _ hα c).mono ?_))
      (fun τ i j v hv => ((hG v hv τ).1 i j).continuousAt.continuousWithinAt) fun v hv τ => (hG v hv τ).2]
  · refine setLIntegral_congr_fun ((bsL ε).continuous.measurable hTi) fun w hw => ?_
    have hw' := Set.image_mono hTO hw
    beta_reduce
    rw [GlobalTheory.T.topDegreeDensity_base_form_times_fibre_class ι m _ _ ε _ _ w (fun τ => (hG _ hw' τ).2) fun τ => (hG _ hw' τ).1.of_le (by norm_cast),
      Complex.re_mul_ofReal, mul_assoc]
  · rintro _ ⟨x, hx, rfl⟩
    exact c.e.map_source (hOc hx)
  · intro x hx
    refine ⟨(GlobalTheory.T.flagCellCoordinates_contDiffAt_etaleChart F σ X Y ι m E E' φ f hf hR c A u _ ε x hx).differentiableAt two_ne_zero, ?_⟩
    rw [Pi.mul_apply, cellForm, map_mul, GlobalTheory.T.pullback_base_form_flag_cell_coordinates F σ X Y ι m E E' φ f hf hR c A u _ ε α hα x hx]
    congr 1
    exact GlobalTheory.T.pullback_aeval_evenComplexForms _ _ _ _ _ _ _ (GlobalTheory.T.graded_line_first_chern_forms_pullback_cell F σ X Y ι m E E' φ f hf hR c A u H hH ε x hx)

end GlobalTheory.FlagCell2.LocFib
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurvaturePowerSumsDbarCohomologous
section
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc.PowCoh

variable {M : Type} [TopologicalSpace M] {n : ℕ} {A : HolAtlas M n} {r : Type} [Fintype r] [DecidableEq r]
  {G G' : M → M → Matrix r r ℂ}

theorem pair_symm (h : IsGramPair A G G') : IsGramPair A G' G :=
  ⟨fun y => (h.smooth y).symm, fun y => (h.trans y).mono fun _ ⟨T, K, K', hT, hK, hK', e⟩ =>
    ⟨T, K', K, hT, hK', hK, e.mono fun _ hw => hw.symm⟩⟩

theorem smooth_crd (h : IsGramPair A G G') (x : A.Pt) :
    MContDiffAt ∞ (fun u => G x.pt (x.ch.symm u)) x.crd ∧ IsUnit (G x.pt (x.ch.symm x.crd)).det := by
  refine ⟨((h.smooth x.pt).1.2 x.1.1 x.2).self_of_nhds, ?_⟩
  rw [x.ch.left_inv x.2]
  exact (h.smooth x.pt).1.1

theorem dbar_powFld (h : IsGramPair A G G') (k : ℕ) : A.dbar (fld A (powFld A G k)) = 0 := by
  funext x
  have h₁ := smooth_crd h x
  refine ((GlobalTheory.T.dbar_operator_local_calculus_complex_forms n x.crd).1 _ _ ((GlobalTheory.T.gramConnectionPair_chernFields_local_frame M n A r G G' h x k).mono fun _ hv => hv.1)).trans ?_
  exact (GlobalTheory.T.curvature_power_sum_transgression_smooth_dbar_closed n r _ _ x.crd h₁.1 h₁.2 h₁.1 h₁.2 k).2.1

theorem dbar_transFld (h : IsGramPair A G G') (k : ℕ) :
    fld A (powFld A G k) - fld A (powFld A G' k) = A.dbar (transFld A G G' k) := by
  funext x
  have h₁ := smooth_crd h x
  have h₂ := smooth_crd (pair_symm h) x
  symm
  refine ((GlobalTheory.T.dbar_operator_local_calculus_complex_forms n x.crd).1 _ _ ((GlobalTheory.T.gramConnectionPair_chernFields_local_frame M n A r G G' h x k).mono fun _ hv => hv.2.2)).trans ?_
  exact GlobalTheory.T.dbar_chernTransgressionForm_eq_power_sum_diff n r _ _ x.crd h₁.1 h₁.2 h₂.1 h₂.2 k

theorem dbarCoh_powFld : ∀ (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n) (r : Type) [Fintype r]
    [DecidableEq r] (G G' : M → M → Matrix r r ℂ), IsGramPair A G G' → ∀ k,
    DbarCoh A (powFld A G k) (powFld A G' k) := fun M _ n A r _ _ G G' h k =>
  ⟨(GlobalTheory.T.curvaturePowerSum_transgression_isForm M n A r G G' h k).1, (GlobalTheory.T.curvaturePowerSum_transgression_isForm M n A r G' G (pair_symm h) k).1, dbar_powFld h k,
    dbar_powFld (pair_symm h) k, _, (GlobalTheory.T.curvaturePowerSum_transgression_isForm M n A r G G' h k).2, dbar_transFld h k⟩

end GlobalTheory.ChernCalc.PowCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerThetaCoefficientEqConstMulMonomialStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eighthPower_thetaCoefficient_eq_const_mul_monomial : ∀ (g l : ℕ), l.Prime → Odd l → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ (V V₁ : Type) [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → IsUnit (l : V₁) → ∀ (Q : Data V), Q.g ≤ g → ∀ (ρ : V →+* V₁), Function.Injective ρ → ∀ (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X), SharpRef W Q ρ D e → ∀ (C : Type) (u : (Fin 8 → Q.X) → C → V₁) (mo : (Fin 8 → Q.X) → V₁), (∀ mu, mo mu ≠ 0 ∧ ∃ c, IsUnit (u mu c)) → IsThetaTerms D ((l ^ j) ^ 2) e (fun mu c => u mu c * mo mu) → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → ∀ (τ₀ : Gens Q) (m N : ℕ) (s : Fin m ⊕ Fin N → V) (ε : Fin m ⊕ Fin N → LinearMap.BilinForm ℤ Q.X), (∀ k, IsUnit (s (.inr k))) → (∀ k mu, 0 ≤ qW W (ε (.inl k)) mu) → TauIn Q τ₀ (fun k => s (finSumFinEquiv.symm k)) (fun k => ε (finSumFinEquiv.symm k)) → (∀ mu, mo mu = mono W (fun k => ρ (s (.inl k))) (fun k => ε (.inl k)) mu) → ∀ (W₀ : Type) [CommRing W₀] (ib : W₀ →+* V), FromBase Q τ₀ ib → (∀ a, ev (ρ (ib a)) ∈ k₀) → ∀ mu c, ∃ r ∈ k₀, ev (u mu c) = r * ∏ k, ev (ρ (s (.inr k))) ^ qW W (ε (.inr k)) mu := by
  first | exact @GlobalTheory.Poinc.Sep.Coef.coef_monomial | exact GlobalTheory.Poinc.Sep.Coef.coef_monomial | (intros; apply GlobalTheory.Poinc.Sep.Coef.coef_monomial <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerTraitUniformisationLatticePowEightStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Poinc Formalism.L2.Pj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eighthPower_trait_uniformisation_lattice_pow_eight : (∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (T : Trait F) (P : PolAV (Sp (FractionRing T.V))) (ε : Matrix (Fin 8) (Fin 8) ℤ → (P.A ⟶ P.A)), IsDiagEnd F W P T.y ε → ∃ (G' : Over (Sp T.V)) (_ : GrpObj G') (_ : IsCommMonObj G'), IsSemiAbelian G' ∧ ∃ (D' : DegData T.V (maximalIdeal T.V)) (U' : Unif (maximalIdeal T.V) D' P G') (j : D'.toPre.X ≃+ (Fin 8 → T.D.toPre.X)), (∀ y, ∃ v : T.Vˣ, PsiCoord D'.toPre y (v * T.ϖ ^ (qW W T.β (j y)).toNat)) ∧ ∀ (K : Type) [Field K] [IsAlgClosed K] [Algebra (FractionRing T.V) K] (m : ℕ) (pk pk' : QkPt D'.toPre K m) (x x' : TFK (R := T.V) K ⟶ P.A) (E : Matrix (Fin 8) (Fin 8) ℤ), 1 ≤ m → QkToAkU U'.toUnifPre K m pk x → QkToAkU U'.toUnifPre K m pk' x' → x' = x ≫ ε E → CongMod m (j pk'.y) (fun a => ∑ b, E a b • j pk.y b)) := by
  first | exact @GlobalTheory.EighthTorsion.main | exact GlobalTheory.EighthTorsion.main | (intros; apply GlobalTheory.EighthTorsion.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveFrobeniusPullbackCotangentModVerscStatement
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_additive_frobeniusPullback_cotangent_mod_verschiebung : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (h : (p : K) = 0) (G : PDivGroup p K), ∀ w : Cot K ((frobTwist h G).A 1), ∃ (β : (frobTwist h G).A 1) (w' : Cot K (G.A 1)), cobOne K (G.A 1) ((relFrob h G).app 1 β) = 0 ∧ dUnit K β = w + cotMap ((verschiebung h G).app 1) w' := by
  first | exact @GlobalTheory.PDivGroup.exists_cobOne_relFrob_eq_zero_dUnit_eq | exact GlobalTheory.PDivGroup.exists_cobOne_relFrob_eq_zero_dUnit_eq | (intros; apply GlobalTheory.PDivGroup.exists_cobOne_relFrob_eq_zero_dUnit_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAmplePowSectionNonvanishingOnClosedStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ample_pow_section_nonvanishing_on_closed : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ T : Set X, IsClosed T → (∀ ℓ : ℕ, (T ∩ fib X ℓ).Finite) → ∃ e : ℕ, 0 < e ∧ ∃ f ∈ P.H e 0, T ⊆ NV P e 0 f := by
  first | exact @GlobalTheory.HSAmp.exists_pow_section_nonvanishing_on_closed | exact GlobalTheory.HSAmp.exists_pow_section_nonvanishing_on_closed | (intros; apply GlobalTheory.HSAmp.exists_pow_section_nonvanishing_on_closed <;> assumption)
end

