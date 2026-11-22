import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0345
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalDualityFiniteDiscreteModules
import Formalism.GaloisCohomology.LocalTateDualityK
import ReciprocityTheory.Hypotheses.GalCohDefs
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousAlgebraMapPadicInt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0305
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0341
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedIntegersTensorEqLetterwiseProductAinf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaBdRPlusSurjectiveKerUnitsEquivariant
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0340
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0319
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0339
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
import GroundTheory.LocalFields.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimePowSmulMemOfTwistedInvariantModLattice
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalDualityPerfectPairFiniteModules
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.LocalPair

theorem exists_dual_equiv {n : ℕ} [NeZero n] {M : Type} [AddCommGroup M] [Module (ZMod n) M] [Finite M]
    {M' : Type} [AddCommGroup M'] [Module (ZMod n) M'] [Finite M'] (P : M →+ M' →+ ZMod n)
    (h1 : ∀ x, (∀ y, P x y = 0) → x = 0) (h2 : ∀ y, (∀ x, P x y = 0) → y = 0) :
    ∃ e : M' ≃+ TDual (ZMod n) M, ∀ y x, e y x = P x y := by
  let f : M' →+ TDual (ZMod n) M := AddMonoidHom.mk'
    (fun y => TDual.mk ((P.flip y).toZModLinearMap n)) (fun y y' => by ext x; simp)
  have hf : ∀ y x, f y x = P x y := fun _ _ => rfl
  have inj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    refine h2 y fun x => ?_
    rw [← hf, hy]
    rfl
  have c1 : Nat.card (TDual (ZMod n) M) = Nat.card M := GlobalTheory.ZModDual.card_dual_eq n M
  have : Finite (TDual (ZMod n) M) := Nat.finite_of_card_ne_zero (by rw [c1]; exact Nat.card_pos.ne')
  have c2 : Nat.card (Module.Dual (ZMod n) M') = Nat.card M' := GlobalTheory.ZModDual.card_dual_eq n M'
  have : Finite (Module.Dual (ZMod n) M') := Nat.finite_of_card_ne_zero (by rw [c2]; exact Nat.card_pos.ne')
  have c3 : Nat.card M ≤ Nat.card M' := by
    rw [← c2]
    refine Nat.card_le_card_of_injective (fun x => ((P x).toZModLinearMap n : Module.Dual (ZMod n) M')) ?_
    intro x x' hx
    rw [← sub_eq_zero]
    refine h1 _ fun y => ?_
    rw [map_sub, AddMonoidHom.sub_apply, sub_eq_zero]
    exact DFunLike.congr_fun hx y
  exact ⟨AddEquiv.ofBijective f (inj.bijective_of_nat_card_le (c1 ▸ c3)), hf⟩

theorem dual_equivariant {n : ℕ} {Λ D : Type} [CommRing Λ] [Group D]
    {M : Type} [AddCommGroup M] [Module (ZMod n) M] [Module Λ M] {M' : Type} [AddCommGroup M'] [Module Λ M']
    (ρ : Representation Λ D M) (ρ' : Representation Λ D M') (P : M →+ M' →+ ZMod n) (χ : D →* (ZMod n)ˣ)
    (hP : ∀ g x y, P (ρ g x) (ρ' g y) = (χ g : ZMod n) * P x y) (e : M' ≃+ TDual (ZMod n) M)
    (he : ∀ y x, e y x = P x y) (g : D) (y : M') : e (ρ' g y) = twDual χ (zmodRep n ρ) g (e y) := by
  ext x
  rw [twDual_apply, he, he]
  change _ = _ * P (ρ g⁻¹ x) y
  rw [← hP, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

section Transport

variable {R R' : Type} [CommRing R] [CommRing R'] {D : Type} [Group D] [TopologicalSpace D]
  {M : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
  {M' : Type} [AddCommGroup M'] [Module R' M'] [TopologicalSpace M'] [DiscreteTopology M']
  (ρ : Representation R D M) (ρ' : Representation R' D M') (e : M ≃+ M')
  (he : ∀ g m, e (ρ g m) = ρ' g (e m))

private def cocycleTransport : Z1 ρ ≃+ Z1 ρ' where
  toFun z := ⟨fun g => e (z.1 g), continuous_of_discreteTopology.comp z.2.1, fun g h => by
    beta_reduce
    rw [z.2.2, map_add, he]⟩
  invFun z := ⟨fun g => e.symm (z.1 g), continuous_of_discreteTopology.comp z.2.1, fun g h => by
    apply e.injective
    rw [map_add, he]
    simp only [AddEquiv.apply_symm_apply]
    exact z.2.2 g h⟩
  left_inv z := Subtype.ext (funext fun g => e.symm_apply_apply _)
  right_inv z := Subtype.ext (funext fun g => e.apply_symm_apply _)
  map_add' z w := Subtype.ext (funext fun g => map_add e _ _)

include he in

private theorem exists_H1_transport : ∃ T : H1 ρ ≃+ H1 ρ', ∀ (z : Z1 ρ) (z' : Z1 ρ'),
    (∀ g, z'.1 g = e (z.1 g)) → T (Submodule.Quotient.mk z) = Submodule.Quotient.mk z' := by
  refine ⟨QuotientAddGroup.congr ((B1 ρ).comap (Z1 ρ).subtype).toAddSubgroup
    ((B1 ρ').comap (Z1 ρ').subtype).toAddSubgroup (cocycleTransport ρ ρ' e he) ?_, fun z z' h => ?_⟩
  · ext z'
    constructor
    · rintro ⟨z, hz, rfl⟩
      obtain ⟨m, hm⟩ := (mem_coboundaries1 ρ _).1 hz
      refine (mem_coboundaries1 ρ' _).2 ⟨e m, fun g => ?_⟩
      change e (z.1 g) = _
      rw [← he, ← map_sub]
      exact congrArg e (hm g)
    · intro hz
      obtain ⟨m, hm⟩ := (mem_coboundaries1 ρ' _).1 hz
      refine ⟨(cocycleTransport ρ ρ' e he).symm z', (mem_coboundaries1 ρ _).2 ⟨e.symm m, fun g => ?_⟩,
        (cocycleTransport ρ ρ' e he).apply_symm_apply z'⟩
      apply e.injective
      change e (e.symm (z'.1 g)) = _
      rw [map_sub, he, e.apply_symm_apply, e.apply_symm_apply]
      exact hm g
  · obtain rfl : z' = cocycleTransport ρ ρ' e he z := Subtype.ext (funext h)
    rfl

end Transport

private theorem card_H0_transport {R R' : Type} [CommRing R] [CommRing R'] {D D' : Type} [Group D] [Group D']
    {M : Type} [AddCommGroup M] [Module R M] {M' : Type} [AddCommGroup M'] [Module R' M']
    (ρ : Representation R D M) (ρ' : Representation R' D' M') (φ : D → D')
    (hφ : Function.Surjective φ) (e : M ≃+ M') (he : ∀ g m, e (ρ g m) = ρ' (φ g) (e m)) :
    Nat.card (H0 ρ') = Nat.card (H0 ρ) := by
  refine (Nat.card_congr (e.toEquiv.subtypeEquiv fun m => ?_)).symm
  change (∀ g, ρ g m = m) ↔ ∀ g, ρ' g (e m) = e m
  rw [hφ.forall]
  refine forall_congr' fun g => ?_
  rw [← he, e.injective.eq_iff]

theorem local_pair : LocalFiniteness → LocalTateDuality → LocalEulerChar → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → ∀ (Λ : Type) [CommRing Λ] (W : Type) [AddCommGroup W] [Module Λ W] [TopologicalSpace W] [DiscreteTopology W] [Finite W] (W' : Type) [AddCommGroup W'] [Module Λ W'] [TopologicalSpace W'] [DiscreteTopology W'] [Finite W'] (ρ : Representation Λ (Dec (F := F) A) W) (ρ' : Representation Λ (Dec (F := F) A) W') (P : W →+ W' →+ ZMod (l ^ n)), 0 < n → ContAction ρ → ContAction ρ' → (∀ x, (∀ y, P x y = 0) → x = 0) → (∀ y, (∀ x, P x y = 0) → y = 0) → (∀ g x y, P (ρ g x) (ρ' g y) = ((cycMod F Ω l n g.1 : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) * P x y) → (∀ y : Z1 ρ', (∀ x : Z1 ρ, CupB (fun g : Dec (F := F) A => ((cycMod F Ω l n g.1 : (ZMod (l ^ n))ˣ) : ZMod (l ^ n))) (fun g m => ρ' g m) P x.1 y.1) ↔ Cob ρ' y.1) ∧ (((l : ℕ) : 𝓞 F) ∉ v.asIdeal → Nat.card (H1 ρ) = Nat.card (H0 ρ) * Nat.card (H0 ρ')) := by
  intro hLF hLD hLE F Ω _ _ _ _ _ l _ n A v hA Λ _ W _ _ _ _ _ W' _ _ _ _ _ ρ ρ' P hn hρ hρ' h1 h2 hP
  have : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have : Module (ZMod (l ^ n)) W := AddCommGroup.zmodModule fun x => h1 _ fun y => by
    rw [map_nsmul, AddMonoidHom.nsmul_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  have : Module (ZMod (l ^ n)) W' := AddCommGroup.zmodModule fun y => h2 _ fun x => by
    rw [map_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  let χ := (cycMod F Ω l n).comp (Dec (F := F) A).subtype
  refine ⟨fun y => ⟨fun H => ?_, ?_⟩, fun hv => ?_⟩
  · obtain ⟨e, he⟩ := exists_dual_equiv P.flip h2 h1
    have hee := dual_equivariant ρ' ρ P.flip χ (fun g y x => hP g x y) e he
    have hinj := (hLD F Ω l n W' A (zmodRep (l ^ n) ρ') v hn hA hρ').2.2.2.1.1
    rw [injective_iff_map_eq_zero] at hinj
    let y' : Z1 ((zmodRep (l ^ n) ρ').comp (MonoidHom.id _)) := ⟨y.1, y.2.1, y.2.2⟩
    have h0 := hinj (Submodule.Quotient.mk y') (by
      refine LinearMap.ext fun x => ?_
      induction x using Submodule.Quotient.induction_on with | H x =>
      obtain ⟨x, rfl⟩ := (cocycleTransport ρ ((twDual χ (zmodRep (l ^ n) ρ')).comp (MonoidHom.id _)) e hee).surjective x
      obtain ⟨f, hf1, hf2⟩ := H x
      refine (Submodule.Quotient.mk_eq_zero _).2 ((separated_dvr_second_cohomology_mem _ _).2 ⟨f, hf1.continuous, funext fun p => ?_⟩)
      exact (hf2 p.1 p.2).symm.trans (he _ _).symm)
    obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 h0)
    exact ⟨m, hm⟩
  · rintro ⟨m, hm⟩ x
    refine ⟨fun g => -P (x.1 g) (ρ' g m), (IsLocallyConstant.iff_continuous _).2 ?_, fun g h => ?_⟩
    · exact ((continuous_of_discreteTopology (f := fun p : W × W' => P p.1 p.2)).comp
        (x.2.1.prodMk (hρ'.comp (continuous_id.prodMk continuous_const)))).neg
    · beta_reduce
      rw [mul_neg, ← hP, x.2.2, hm, map_mul, Module.End.mul_apply]
      simp only [map_add, map_sub, AddMonoidHom.add_apply]
      ring
  · obtain ⟨e, he⟩ := exists_dual_equiv P h1 h2
    have hee := dual_equivariant ρ ρ' P χ hP e he
    obtain ⟨⟨j⟩, -, -, -, hb⟩ := hLD F Ω l n W A (zmodRep (l ^ n) ρ) v hn hA hρ
    have hE := (hLE F Ω l n W A (zmodRep (l ^ n) ρ) v hn hA hρ).2 hv
    obtain ⟨T, -⟩ := exists_H1_transport ρ (zmodRep (l ^ n) ρ) (AddEquiv.refl W) fun _ _ => rfl
    have c0 := card_H0_transport ρ (zmodRep (l ^ n) ρ) id Function.surjective_id (AddEquiv.refl W) fun _ _ => rfl
    have c0' := card_H0_transport ρ' ((twDual χ (zmodRep (l ^ n) ρ)).comp (MonoidHom.id _)) id Function.surjective_id e hee
    have : Finite (TDual (ZMod (l ^ n)) W) := Finite.of_equiv _ e.toEquiv
    rw [Nat.card_congr T.toEquiv, hE, c0, ← c0']
    congr 1
    refine (Nat.card_eq_of_bijective _ hb).trans ?_
    exact (Nat.card_congr (LinearEquiv.congrRight j).toEquiv).trans (GlobalTheory.ZModDual.card_dual_eq _ _)

end GlobalTheory.LocalPair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalInertiaIffMemPlaceInertia
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal

noncomputable section

namespace GlobalTheory.DecInertia

theorem valuation_lt_one_iff_norm {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] {A : ValuationSubring Ω}
    {j : Ω →+* PadicAlgCl p} (hj : ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1) (x : Ω) :
    A.valuation x < 1 ↔ ‖j x‖ < 1 := by
  rw [valuation_lt_one_iff', hj, hj, map_inv₀, norm_inv]
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · have h0 : 0 < ‖j x‖ := norm_pos_iff.mpr ((_root_.map_ne_zero _).mpr hx)
    simp only [hx, false_or, not_le, one_lt_inv₀ h0]
    exact ⟨fun h => h.2, fun h => ⟨h.le, h⟩⟩

theorem inertiaK_iff_mem_Ine (p : ℕ) [Fact p.Prime] (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] (A : ValuationSubring Ω) (j : Ω →+* PadicAlgCl p) (hj : ∀ x, x ∈ A ↔ ‖j x‖ ≤ 1)
    (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    (i : ↥(A.decompositionSubgroup F) ≃* (PadicAlgCl p ≃ₐ[↥K] PadicAlgCl p))
    (hi : ∀ (g : ↥(A.decompositionSubgroup F)) (x : Ω), i g (j x) = j ((g : Ω ≃ₐ[F] Ω) x))
    (g : ↥(A.decompositionSubgroup F)) :
    i g ∈ Formalism.GaloisCohomology.inertiaK p K ↔ (g : Ω ≃ₐ[F] Ω) ∈ Ine (F := F) A := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have hn : ∀ (σ : PadicAlgCl p ≃ₐ[↥K] PadicAlgCl p) (z : PadicAlgCl p), ‖σ z‖ = ‖z‖ := fun σ z =>
    GlobalTheory.PlaceBridge.norm_algEquiv (σ.restrictScalars ℚ_[p]) z
  have hadd : ∀ a b : PadicAlgCl p, ‖a + b‖ ≤ max ‖a‖ ‖b‖ := IsUltrametricDist.norm_add_le_max
  constructor
  · intro h
    let H : Subgroup (PadicAlgCl p ≃ₐ[↥K] PadicAlgCl p) :=
      ((Ine (F := F) A).subgroupOf (A.decompositionSubgroup F)).map i.toMonoidHom
    have hsub : Formalism.GaloisCohomology.inertiaSet p K ⊆ H := by
      intro σ hσ
      refine ⟨i.symm σ, ?_, by simp⟩
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
      refine ⟨(i.symm σ).2, fun x hx => ?_⟩
      rw [valuation_lt_one_iff_norm hj, map_sub, ← hi, MulEquiv.apply_symm_apply]
      exact hσ (j x) ((hj x).1 ((A.valuation_le_one_iff x).1 hx))
    have hle : Formalism.GaloisCohomology.inertiaK p K ≤ H := (Subgroup.closure_le _).2 hsub
    obtain ⟨g', hg', e⟩ := hle h
    have : g' = g := i.injective e
    subst this
    exact Subgroup.mem_subgroupOf.1 hg'
  · intro h
    apply Subgroup.subset_closure
    intro x hx
    obtain ⟨y, hy⟩ := (GlobalTheory.PlaceBridge.denseRange_embedding j).exists_dist_lt x one_pos
    rw [dist_eq_norm] at hy
    have hjy : ‖j y‖ ≤ 1 := by
      have e : j y = x + -(x - j y) := by ring
      rw [e]
      exact (hadd _ _).trans (max_le hx (by rw [norm_neg]; exact hy.le))
    have hgy : ‖(i g) (j y) - j y‖ < 1 := by
      rw [hi, ← map_sub, ← valuation_lt_one_iff_norm hj]
      exact h.2 y ((A.valuation_le_one_iff y).2 ((hj y).2 hjy))
    have e : (i g) x - x = (i g) (x - j y) + (((i g) (j y) - j y) + -(x - j y)) := by
      rw [map_sub]; ring
    rw [e]
    refine (hadd _ _).trans_lt (max_lt (by rw [hn]; exact hy) ((hadd _ _).trans_lt (max_lt hgy ?_)))
    rw [norm_neg]; exact hy

end GlobalTheory.DecInertia
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalInvariantsKilled
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen GlobalTheory.TwSys GlobalTheory.SelFun GlobalTheory.Published GlobalTheory.ResSel GlobalTheory.StepTwo GlobalTheory.TwistDet GlobalTheory.NewPrime GlobalTheory.Published.PoitouTate

namespace GlobalTheory.NewPrime.LocInv

theorem tors_of_finite (A : Type) [CommRing A] [IsLocalRing A] [Finite A] (Y : Type) [AddCommGroup Y] [Module A Y] :
    Tors A Y := by
  intro b
  obtain ⟨n, hn⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := A)
  rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at hn
  refine ⟨n, fun x hx => ?_⟩
  rw [hn] at hx
  rw [(Submodule.mem_bot _).1 hx, zero_smul]

theorem dual_eq_one {D : Formalism.BasicNotions.D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N} (bkP : BKPh X)
    (i : X.Tw) (s : X.Sig i) (h : IsotypicValuationAtRing bkP i s) {ρ : GE N →* GL (Fin D.R.r) (X.O0 i)} (hρ : IsDual i s ρ)
    (v : PlE D.host) (hl : v ∉ placesOver D.host.E (X.l i)) (hS : v ∉ Spl i) (σ : GE N)
    (hσ : σ ∈ Ine (F := D.host.E) (N.plOm.1 v)) : ρ σ = 1 := by
  have hvl : ((X.l i : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal := hl
  have h1 : cycZ D.host.E N.Om (X.l i) σ = 1 := by
    refine Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)
    rw [cycZ_toZModPow_eq hvl (N.plOm.2 v) (q := 1) (fun x hx => by simpa using hσ.2 x hx) n]
    simp
  have h2 : eps0 X i σ = 1 := by
    rw [eps0, MonoidHom.comp_apply, h1, map_one]
  have h3 := GlobalTheory.SelFun.Colim.tgl_eq_one bkP i s h v hl hS _ (N.plOm.2 v) σ hσ
  apply Units.ext
  rw [hρ σ, Tdual, h2, ← Tgl_coe, h3]
  simp

theorem local_invariants_killed : TameLocal → ∀ (D : Formalism.BasicNotions.D7) (N : NData D.R D.host D.what₂) (X : NTw D.R D.host D.what₂ D.LL0 N) (bkP : BKPh X) (i : X.Tw) (s : X.Sig i), 0 < nu X i → ∀ (M R n : ℕ) (d : PlE D.host → (GE N →* Multiplicative (ZMod (X.l i ^ M)))) (A₀ : Finset (PlE D.host)) (L : Subgroup (GE N)) (z : GE N) (P : Fin R ⊕ Fin n → PlE D.host), 1 ≤ M → IsTameInertiaElementAtTwistPrime X i z → Small2 i s M L z → PiLocalization₂ i M d A₀ L z P → ∀ (A : Type) [CommRing A] [IsLocalRing A] [Finite A] [Algebra (X.O0 i) A] (κ : GE N →* Aˣ) (Q : Finset (PlE D.host)) (ρ : GE N →* GL (Fin D.R.r) (X.O0 i)) (t : A) (a : Fin R ⊕ Fin n → A), IsQ P Q → Setup bkP i s κ Q → Kills i A → IsDual i s ρ → IsChar i κ (fun q => a q * t) (fun q => d (P q)) → (∀ q, IsUnit (a (.inr q))) → ∀ (Y : Type) [AddCommGroup Y] [Module A Y] [TopologicalSpace Y] [DiscreteTopology Y], ∀ v, v ∈ Spl i ∨ v ∈ Q → ∀ m, (∀ g ∈ DecV N v, repOn ρ κ⁻¹ Y g m = m) → t • m = 0 := by
  intro _ D N X bkP i s _ M R n d A₀ L z P hM hz hL hSt A _ _ _ _ κ Q ρ t a hQ hSet _ hρ hch ha Y _ _ _ _ v hv m hm
  obtain ⟨hG, hloc, -, hκo, hκl, -, hQl, -⟩ := hSet
  have hκl' : ∀ g, ∃ k : ℕ, κ⁻¹ g ^ (X.l i ^ k) = 1 := fun g => by
    obtain ⟨k, hk⟩ := hκl g
    exact ⟨k, by rw [MonoidHom.inv_apply, inv_pow, hk, inv_one]⟩
  by_cases hS : v ∈ Spl i
  · have hker : (κ⁻¹).ker = κ.ker := by
      ext g
      simp [MonoidHom.mem_ker]
    have h0 := (GlobalTheory.PrimeToInertia.local_cohomology_vanishes D N X bkP i s hG v hS A κ⁻¹ (hker ▸ hκo) hκl' Y
      (tors_of_finite A Y) ρ (Or.inr hρ)).1
    have : m ∈ H0 ((repOn ρ κ⁻¹ Y).comp (DecV N v).subtype) := (mem_riemannRochSpace_iff_regularAt_everywhere _ _).2 fun g => hm g.1 g.2
    rw [h0, Submodule.mem_bot] at this
    rw [this, smul_zero]
  have hvQ : v ∈ Q := hv.resolve_left hS
  obtain ⟨q, hq⟩ := (hQ v).1 hvQ
  rcases q with b | q
  · have hA : ∀ w, Over (P (.inl b)) w → w ∉ X.S0 i ∧ normV w % X.l i = 1 := fun w hw => by
      obtain ⟨-, -, -, h0, -, hn⟩ := hSt.1.1 _ w hw
      exact ⟨h0, mod_l_eq_one i hM hn⟩
    have hp := hA v hq
    have hn := GlobalTheory.ScalarFrob.natCast_eq_one_of_mod i hp.2
    obtain ⟨σ, hσ⟩ := exists_isFrob (N.plOm.2 v)
    obtain ⟨c, c0, c1, hc⟩ := GlobalTheory.ScalarFrob.frob_scalar_place i s bkP hG hz hL.1 hA (hSt.2.1 b).2 hq hσ
    have hc' : ((ρ σ : GL (Fin D.R.r) (X.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)).map (IsLocalRing.residue _) =
        c⁻¹ • 1 := by
      rw [hρ, GlobalTheory.ScalarFrob.dual_of_scalar i s (GlobalTheory.ScalarFrob.eps_frob i hp.1 hn hσ) c0 hc]
    rw [GlobalTheory.ScalarFrob.eq_zero_of_scalar Fact.out (GlobalTheory.PrimeToInertia.l_mem i) ρ κ⁻¹ (hκl' σ) (inv_ne_one.2 c1) hc'
      (q := 1) Nat.cast_one m (by rw [one_smul]; exact hm σ hσ.1), smul_zero]
  · obtain ⟨γ, hγ, hd⟩ := (hSt.1.2.2 (.inr q)).2.2.2.2 v hq _ (N.plOm.2 v) (Multiplicative.ofAdd 1)
    have hρ1 := dual_eq_one bkP i s hG.1 hρ v (hQl v hvQ) hS γ hγ
    have hk := hch γ
    haveI : Fact (1 < X.l i ^ M) := ⟨Nat.one_lt_pow (by omega) (Fact.out : (X.l i).Prime).one_lt⟩
    rw [Finset.prod_eq_single (Sum.inr q)] at hk
    · have hd' : d (P (.inr q)) γ = Multiplicative.ofAdd 1 := hd
      simp only [hd', toAdd_ofAdd, ZMod.val_one, pow_one] at hk
      have hinv : ((κ⁻¹ γ : Aˣ) : A) = 1 + a (.inr q) * t := by
        rw [MonoidHom.inv_apply]
        exact Units.inv_eq_of_mul_eq_one_right hk
      have e := hm γ (Ine_le_Dec _ hγ)
      have e2 : repOn ρ κ⁻¹ Y γ m = (1 + a (.inr q) * t) • m := by
        simp [repOn, hρ1, matAct_one, ← hinv]
      rw [e2, add_smul, one_smul, add_eq_left, mul_smul] at e
      exact ((ha q).smul_eq_zero).1 e
    · intro q' _ hne
      have hn : ¬ Over (P q') v := fun h' => hne (hSt.1.2.1 _ _ (over_trans h' (over_symm hq)))
      have : d (P q') γ = 1 := (hSt.1.2.2 q').2.2.2.1 v hn _ (N.plOm.2 v) γ hγ
      simp [this]
    · simp

end GlobalTheory.NewPrime.LocInv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalPeriodRingsSectionEqAinfToBdRPlus
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.SeedSec

theorem eq_of_pow_eq_self {R K : Type} [CommRing R] [Field K] [CharZero K] (θ : R →+* K)
    (hθ : ∀ y, θ y ≠ 0 → IsUnit y) {n : ℕ} (hn : 2 ≤ n) {u v : R} (hu : u ^ n = u) (hv : v ^ n = v)
    (h : θ u = θ v) : u = v := by
  set S := ∑ i ∈ Finset.range n, u ^ i * v ^ (n - 1 - i) with hS
  have h1 : S * (u - v) = u - v := by rw [hS, geom_sum₂_mul, hu, hv]
  have hc : θ u ^ n = θ u := by rw [← map_pow, hu]
  have e : θ S = n * θ u ^ (n - 1) := by
    rw [hS, map_sum, Finset.sum_congr rfl (g := fun _ => θ u ^ (n - 1)) (fun i hi => by
      have := Finset.mem_range.1 hi
      rw [map_mul, map_pow, map_pow, ← h, ← pow_add]
      congr 1
      omega)]
    simp
  have h2 : θ (S - 1) ≠ 0 := by
    rw [map_sub, map_one, e]
    by_cases h0 : θ u = 0
    · rw [h0, zero_pow (by omega)]
      simp
    · have h3 : θ u ^ (n - 1) = 1 := by
        refine mul_right_cancel₀ h0 ?_
        rw [← pow_succ, Nat.sub_add_cancel (by omega), one_mul, hc]
      rw [h3, mul_one, sub_ne_zero]
      exact_mod_cast (show n ≠ 1 by omega)
  have h4 : (S - 1) * (u - v) = 0 := by rw [sub_mul, h1, one_mul, sub_self]
  exact sub_eq_zero.1 ((hθ _ h2).mul_right_eq_zero.1 h4)

theorem exists_om_of_pow_eq_self (l : ℕ) [Fact l.Prime] {n : ℕ} (hn : 2 ≤ n) (c : ℂ_[l]) (hc : c ^ n = c) :
    ∃ x : Om l, algebraMap (Om l) ℂ_[l] x = c := by
  have hs : (Polynomial.X ^ n - Polynomial.X : Polynomial (Om l)).Splits := IsAlgClosed.splits _
  have h0 : (Polynomial.X ^ n - Polynomial.X : Polynomial (Om l)) ≠ 0 := fun h => by
    have := congrArg (Polynomial.coeff · 1) h
    simp [Polynomial.coeff_X_pow, show (1 : ℕ) ≠ n by omega] at this
  obtain ⟨x, hx⟩ := hs.mem_range_of_isRoot h0 (i := algebraMap (Om l) ℂ_[l]) (x := c) (by simp [hc])
  exact ⟨x, hx⟩

private theorem padicInt_hom_apply_eq {l : ℕ} [Fact l.Prime] {R : Type} [CommRing R]
    (hR : IsHausdorff (Ideal.span {(l : R)}) R) (f g : ℤ_[l] →+* R) (z : ℤ_[l]) : f z = g z := by
  rw [← sub_eq_zero]
  refine IsHausdorff.haus hR _ fun n => ?_
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec n z)
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton']
  refine ⟨f c - g c, ?_⟩
  have hf := congrArg f hc
  have hg := congrArg g hc
  simp only [map_mul, map_pow, map_natCast, map_sub] at hf hg
  linear_combination hf - hg

theorem exists_sec (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (C : Core l) (w : Wq l a) :
    ∃ x : Om l, ((Per.θ l (wA l a w) : OC l) : ℂ_[l]) = algebraMap (Om l) ℂ_[l] x ∧
      C.o x = aDp l (wA l a w) := by
  have hspan : w ∈ Submodule.span ℤ_[l] (Set.range (WittVector.teichmuller l : Fq l a → Wq l a)) := by
    rw [span_teich]; trivial
  induction hspan using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨z, rfl⟩ := hy
    have hq : 2 ≤ l ^ a := one_lt_pow_l l a
    have hw : (WittVector.teichmuller l z) ^ (l ^ a) = WittVector.teichmuller l z := by
      rw [← map_pow, Fq.pow_card]
    set A := wA l a (WittVector.teichmuller l z) with hAdef
    have hA : A ^ (l ^ a) = A := by rw [hAdef, ← map_pow, hw]
    have hc : ((Per.θ l A : OC l) : ℂ_[l]) ^ (l ^ a) = ((Per.θ l A : OC l) : ℂ_[l]) := by
      rw [← SubmonoidClass.coe_pow, ← map_pow, hA]
    obtain ⟨x, hx⟩ := exists_om_of_pow_eq_self l hq _ hc
    have hxq : x ^ (l ^ a) = x := (algebraMap (Om l) ℂ_[l]).injective (by rw [map_pow, hx, hc])
    refine ⟨x, hx.symm, eq_of_pow_eq_self (Per.θD l) (thetaD_props l).2.2.1 hq
      (by rw [← map_pow, hxq]) (by rw [← map_pow, hA]) ?_⟩
    rw [C.o_sec.th, (thetaD_props l).2.2.2.1]
    exact hx
  | zero => exact ⟨0, by simp, by simp⟩
  | add y y' _ _ hy hy' =>
    obtain ⟨x, hx1, hx2⟩ := hy
    obtain ⟨x', hx1', hx2'⟩ := hy'
    refine ⟨x + x', ?_, ?_⟩
    · rw [map_add, map_add, map_add, Subring.coe_add, hx1, hx1']
    · rw [map_add, map_add, map_add, hx2, hx2']
  | smul r y _ hy =>
    obtain ⟨x, hx1, hx2⟩ := hy
    have e : wA l a (r • y) = algebraMap ℤ_[l] (Ainf l) r * wA l a y := by
      rw [map_smul, Algebra.smul_def]
    refine ⟨algebraMap ℚ_[l] (Om l) (r : ℚ_[l]) * x, ?_, ?_⟩
    · rw [e, map_mul, Subring.coe_mul, hx1, map_mul]
      congr 1
      exact GlobalTheory.UnramIdem.ringHom_eq ((Per.θ l).comp (algebraMap ℤ_[l] (Ainf l))) r
    · rw [e, map_mul, map_mul, hx2, C.o_sec.z r]
      have hA : IsAdicComplete (Ideal.span {(l : Ainf l)}) (Ainf l) := inferInstance
      rw [padicInt_hom_apply_eq hA.toIsHausdorff (Per.zA l) (algebraMap ℤ_[l] (Ainf l)) r]

theorem o_eq_aDp_wA : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ) [NeZero a] (C : Core l) (w : Wq l a) (x : Om l),
    ((Per.θ l (wA l a w) : OC l) : ℂ_[l]) = (x : ℂ_[l]) → C.o x = aDp l (wA l a w) := by
  intro l _ a _ C w x hx
  obtain ⟨y, hy1, hy2⟩ := exists_sec l a C w
  have hxy : x = y := (algebraMap (Om l) ℂ_[l]).injective (hx.symm.trans hy1)
  rw [hxy, hy2]

end GlobalTheory.SeedSec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixPhiEquationToFamilyEquation
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

theorem GlobalTheory.BSP.matrix_phi_eq_family : ∀ (R C : Type) [CommRing R] [CommRing C] (i : R →+* C) (φ : C → C) (e e' : R), Associated e e' → ∀ (d d' a a' b : ℕ) (P : Matrix (Fin d') (Fin d') R) (Q Q' : Matrix (Fin d) (Fin d) R), Q * Q' = e' ^ b • (1 : Matrix (Fin d) (Fin d) R) → ∀ Δ : Matrix (Fin d') (Fin d) C, i e' ^ a • (P.map i * Δ.map φ) = i e ^ a' • (Δ * Q.map i) → ∃ (h : ℕ) (c : Fin d' × Fin d → Fin d' × Fin d → R), ∀ j : Fin d' × Fin d, i e ^ h * Δ j.1 j.2 = ∑ k : Fin d' × Fin d, φ (Δ k.1 k.2) * i (c k j) := by
  intro R C _ _ i φ e e' he d d' a a' b P Q Q' hQ Δ hΔ
  obtain ⟨u, hu⟩ := he
  have hQm : Q.map i * Q'.map i = (i e') ^ b • (1 : Matrix (Fin d) (Fin d) C) := by
    rw [← Matrix.map_mul, hQ]
    ext x y
    by_cases hxy : x = y <;> simp [Matrix.one_apply, hxy]
  have key : (i e' ^ a • (P.map i * Δ.map φ)) * Q'.map i
      = (i e ^ a' • (Δ * Q.map i)) * Q'.map i := by rw [hΔ]
  rw [Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_assoc Δ, hQm, Matrix.mul_smul, Matrix.mul_one] at key
  refine ⟨a' + b, fun k j => ((u⁻¹ : Rˣ) : R) ^ b * e' ^ a * P j.1 k.1 * Q' k.2 j.2, ?_⟩
  intro j
  have hj := congrFun (congrFun key j.1) j.2
  simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.map_apply, smul_eq_mul, Finset.sum_mul] at hj
  rw [Finset.sum_comm] at hj
  have hu' : i e' = i e * i (u : R) := by rw [← hu, map_mul]
  have hinv : i ((u⁻¹ : Rˣ) : R) * i (u : R) = 1 := by rw [← map_mul, Units.inv_mul, map_one]
  have goalR : ∑ k : Fin d' × Fin d, φ (Δ k.1 k.2) * i (((u⁻¹ : Rˣ) : R) ^ b * e' ^ a * P j.1 k.1 * Q' k.2 j.2)
      = i ((u⁻¹ : Rˣ) : R) ^ b * (i e' ^ a * ∑ k1 : Fin d', ∑ k2 : Fin d, i (P j.1 k1) * φ (Δ k1 k2) * i (Q' k2 j.2)) := by
    rw [Fintype.sum_prod_type, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k1 _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k2 _ => ?_
    simp only [map_mul, map_pow]; ring
  rw [goalR, hj, hu', mul_pow]
  calc i e ^ (a' + b) * Δ j.1 j.2
      = (i ((u⁻¹ : Rˣ) : R) * i (u : R)) ^ b * (i e ^ (a' + b) * Δ j.1 j.2) := by rw [hinv, one_pow, one_mul]
    _ = _ := by ring
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanRestrictionLatticeColumnsStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon GlobalTheory.PMon.ResR TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_span_restrictionLattice_columns : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (r : ℕ), 0 < r → ∀ (ω : Fin r → ↥(MaximalUnramifiedExtension l)), (∀ k, fr l r (ω k) = ω k) → ∀ (hdet : (frobMat ω).det ≠ 0) (n : Type) [Fintype n] [DecidableEq n] (U : Fin r → GL n P.R.BdR) (x y : Fin r × n) (A₀ : GL (n × Fin r) P.R.B), (∀ i j, P.φB ((A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) i j) = (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B) i j) → ∀ W₀ : GL (n × Fin r) P.R.BdR, UnitM P W₀ → (A₀ : Matrix (n × Fin r) (n × Fin r) P.R.B).map (ev P 0) = (U0 P ω hdet U : Matrix (n × Fin r) (n × Fin r) P.R.BdR) * Matrix.diagonal (fun j : n × Fin r => tz P (eps x y (j.2, j.1))) * (W₀ : Matrix (n × Fin r) (n × Fin r) P.R.BdR) → ∀ a : n → P.R.B, LatC P U x y a → a ∈ Submodule.span ℚ_[l] (Set.range (colv P ω A₀)) := by
  first | exact @GlobalTheory.PMon.ResR.mem_span_colv | exact GlobalTheory.PMon.ResR.mem_span_colv | (intros; apply GlobalTheory.PMon.ResR.mem_span_colv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonVEqZeroIffExistsCrisInclStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monV_eq_zero_iff_mem_range_crisIncl' : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] (z : V ⊗[ℚ_[l]] Bst P), monV P ℚ_[l] V z = 0 ↔ ∃ w, crisIncl P ℚ_[l] V w = z := by
  first | exact @GlobalTheory.PMon.monV_eq_zero_iff_exists_crisIncl | exact GlobalTheory.PMon.monV_eq_zero_iff_exists_crisIncl | (intros; apply GlobalTheory.PMon.monV_eq_zero_iff_exists_crisIncl <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormalizedValuationOfPrimeOfGaloisExtensionStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalizedValuationOfPrime_of_galoisExtension : ∀ (F L : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] [Algebra F L] [ValuativeExtension F L] [FiniteDimensional F L] [IsGalois F L] (p E : ℕ), OrdIs L p E → ∃ e : ℕ, OrdIs F p e ∧ E = ramificationIndex F L * e ∧ ramificationIndex F L = Nat.card ↥(lowerRamificationGroup F L 0) := by
  first | exact @GlobalTheory.PMon.Ram.ordIs_of_ordIs_ext | exact GlobalTheory.PMon.Ram.ordIs_of_ordIs_ext | (intros; apply GlobalTheory.PMon.Ram.ordIs_of_ordIs_ext <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowPrimeMemUnitFiltrationUnitsMinStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pow_prime_mem_unitFiltrationUnits_min : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (p e n : ℕ), OrdIs F p e → ∀ x ∈ unitFiltrationUnits F n, x ^ p ∈ unitFiltrationUnits F (min (2 * n) (n + e)) := by
  first | exact @GlobalTheory.PMon.Ram.pow_mem_unitFiltrationUnits | exact GlobalTheory.PMon.Ram.pow_mem_unitFiltrationUnits | (intros; apply GlobalTheory.PMon.Ram.pow_mem_unitFiltrationUnits <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrimePowSmulMemOfTwistedInvariantModLatticeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.prime_pow_smul_mem_of_twistedInvariant_mod_lattice : ∀ (l : ℕ) [Fact l.Prime] (act : GQ l →* (PadicComplex l ≃+* PadicComplex l)) (χ : GQ l →* ℚ_[l]ˣ), IsActC act → IsCyc χ → ∀ (K : FinExt l), ∀ (m r : ℕ), Lev l m → ∀ (U : GQ l → Matrix (Fin r) (Fin r) (PadicComplex l)) (g : GQ l), Frame χ K m U g → ∀ J : Finset ℤ, HTBasis act χ (Gj K m) U (J : Set ℤ) → ∀ (i : ℤ), i ∉ J → ∀ M : AddSubgroup (Fin r → PadicComplex l), ball l r ⊆ (M : Set _) → (∀ x ∈ M, (l : PadicComplex l) • x ∈ ball l r) → ∀ y : Fin r → PadicComplex l, (∀ σ ∈ Gj K m, twAct act χ i U σ y - y ∈ M) → (l : PadicComplex l) ^ (2 + max 1 (∑ u ∈ J.erase i, (m + padicValInt l (u - i)))) • y ∈ M := by
  first | exact @GlobalTheory.FrameInv.pow_smul_mem_of_invariant_mod | exact GlobalTheory.FrameInv.pow_smul_mem_of_invariant_mod | (intros; apply GlobalTheory.FrameInv.pow_smul_mem_of_invariant_mod <;> assumption)
end

