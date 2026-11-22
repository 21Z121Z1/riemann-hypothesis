import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1621
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1588
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1600
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1598
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0041
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0034
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1624
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1606
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1644
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.HodgeTateKernel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1640
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MulEqZeroOfToCompletion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1036
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0257
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0435
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1051
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1332
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1025
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1019
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1086
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1625
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0957
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InjectiveOfSmulMemRange

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisibleAlgClosureOfKillsTorsionSepClosed
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SepClosedDivisible

theorem divisible_algClosure : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosed Ω] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ m : ℕ, (m : K) ≠ 0 → ∀ f : A ⟶ A, IsMonHom f → (∀ x : ptOver K Ω ⟶ A, x ^ m = 1 → x ≫ f = 1) → ∃ h : (Over.pullback (spMap (algebraMap K (AlgebraicClosure Ω)))).obj A ⟶ (Over.pullback (spMap (algebraMap K (AlgebraicClosure Ω)))).obj A, IsMonHom h ∧ (Over.pullback (spMap (algebraMap K (AlgebraicClosure Ω)))).map f = h ^ m := by
  intro K Ω _ _ _ _ A _ hA m hm f hf hkill
  set L := AlgebraicClosure Ω
  set t : Sp L ⟶ Sp K := spMap (algebraMap K L) with ht
  let j : Ω →ₐ[K] L := IsScalarTower.toAlgHom K Ω L
  have hmL : (m : L) ≠ 0 := by
    intro h; apply hm; apply (algebraMap K L).injective; simpa using h
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (by simp)
  obtain ⟨g, hg⟩ := GlobalTheory.AbVarRelDim.exists_relDim K A hA
  have hcΩ := GlobalTheory.SepClosedTorsion.card_torsion_sepClosed K Ω A hA g hg m hm
  have hcL := GlobalTheory.SepClosedTorsion.card_torsion_eq (Ω := Ω) (Ω' := L) A hA hm
  have hpos : m ^ (2 * g) ≠ 0 := pow_ne_zero _ hm0
  haveI : Finite {x : ptOver K L ⟶ A // x ^ m = 1} := Nat.finite_of_card_ne_zero (by rw [← hcL, hcΩ]; exact hpos)
  let emb : (ptOver K Ω ⟶ A) →* (ptOver K L ⟶ A) := MonoidHom.mk' (fun x => ptOverMap j ≫ x) fun x y => MonObj.comp_mul _ x y
  have hemb : Function.Injective emb := by
    intro x y e
    have := epi_ptOverMap j
    exact Over.OverMorphism.ext ((cancel_epi (ptOverMap j).left).1
      (by simpa using congrArg (fun q => q.left) (show ptOverMap j ≫ x = ptOverMap j ≫ y from e)))
  let emb' : {x : ptOver K Ω ⟶ A // x ^ m = 1} → {x : ptOver K L ⟶ A // x ^ m = 1} :=
    fun x => ⟨emb x.1, by rw [← map_pow, x.2, map_one]⟩
  have hemb' : Function.Injective emb' := fun x y e => Subtype.ext (hemb (congrArg Subtype.val e))
  have hbij := hemb'.bijective_of_nat_card_le hcL.ge
  have step1 : ∀ y : ptOver K L ⟶ A, y ^ m = 1 → y ≫ f = 1 := by
    intro y hy
    obtain ⟨x, hx⟩ := hbij.2 ⟨y, hy⟩
    have hx' : ptOverMap j ≫ x.1 = y := congrArg Subtype.val hx
    rw [← hx', Category.assoc, hkill x.1 x.2, MonObj.comp_one]
  have hgp : IsGrpPullback ((Over.pullback t).obj A) A t (pullback.fst A.hom t) := isGrpPullback_pullback A t
  have hB : IsAbelianScheme ((Over.pullback t).obj A) := GlobalTheory.isAbelianScheme_pullback_obj t A hA
  obtain ⟨e, he⟩ := GlobalTheory.exists_mulEquiv_of_isGrpPullback hgp (𝟙 (Sp L)) t (Category.id_comp t).symm
  have hFf : IsMonHom ((Over.pullback t).map f) := inferInstance
  refine (GlobalTheory.TorsionDivisible.finite_torsion_and_divisible L _ hB m hmL).2 _ hFf ?_
  intro x hx
  apply e.injective
  have h1 : e x ^ m = 1 := by rw [← map_pow, hx, map_one]
  have h2 : e x ≫ f = 1 := step1 (e x) h1
  rw [map_one, ← h2]
  apply Over.OverMorphism.ext
  rw [he, Over.comp_left, Over.comp_left, he]
  simp
  rw [pullback.lift_fst]

end GlobalTheory.SepClosedDivisible

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrFractionFieldRingEquivEqUnitMulStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dvr_fractionField_ringEquiv_eq_unit_mul : ∀ (W K' : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field K'] [Algebra W K'] [IsFractionRing W K'] (σ : K' ≃+* K'), (∀ x : W, ∃ y : W, σ (algebraMap W K' x) = algebraMap W K' y) → (∀ x : W, ∃ y : W, σ.symm (algebraMap W K' x) = algebraMap W K' y) → ∀ l : K', l ≠ 0 → ∃ a : W, σ l = algebraMap W K' a * l := by
  first | exact @GlobalTheory.dvr_fractionField_ringEquiv_eq_mul | exact GlobalTheory.dvr_fractionField_ringEquiv_eq_mul | (intros; apply GlobalTheory.dvr_fractionField_ringEquiv_eq_mul <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenFinrankOfCokernel
section
set_option autoImplicit false

noncomputable section

open GlobalTheory GlobalTheory.HTLat GlobalTheory.PDivGroup GlobalTheory.WeilIntegral GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateKernel TensorProduct CategoryTheory ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ChTor CategoryTheory.MonObj

namespace GlobalTheory.HodgeTateEigenRank

section Algebra

variable {O C : Type} [CommRing O] [IsDomain O] [Field C] [Algebra O C] [IsFractionRing O C]
  {V : Type} [AddCommGroup V] [Module C V] [Module O V] [IsScalarTower O C V]

theorem exists_smul_mem_of_mem_span (N : Submodule O V) {x : V}
    (hx : x ∈ Submodule.span C (N : Set V)) : ∃ s : O, s ≠ 0 ∧ s • x ∈ N := by
  induction hx using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by rwa [one_smul]⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hx⟩ := hx
    obtain ⟨b, hb, hy⟩ := hy
    refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
    rw [smul_add]
    refine Submodule.add_mem _ ?_ ?_
    · rw [mul_comm, mul_smul]; exact Submodule.smul_mem _ _ hx
    · rw [mul_smul]; exact Submodule.smul_mem _ _ hy
  | smul c x _ hx =>
    obtain ⟨r, hr, hx⟩ := hx
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors O) c
    refine ⟨b * r, mul_ne_zero (nonZeroDivisors.coe_ne_zero b) hr, ?_⟩
    have h1 : (b : O) • c • x = a • x := by
      rw [← algebraMap_smul C (b : O), smul_smul, mul_comm, hab, algebraMap_smul]
    rw [mul_comm, mul_smul, h1, smul_comm]
    exact N.smul_mem _ hx

theorem finrank_span_range {M : Type} [AddCommGroup M] [Module O M] [Module.Free O M]
    [Module.Finite O M] (B : M →ₗ[O] V) (hB : Function.Injective B) :
    Module.finrank C (Submodule.span C (Set.range B)) = Module.finrank O M := by
  let b := Module.finBasis O M
  have h1 : LinearIndependent O (B ∘ b) :=
    b.linearIndependent.map' B (LinearMap.ker_eq_bot.2 hB)
  have h2 : LinearIndependent C (B ∘ b) := (LinearIndependent.iff_fractionRing O C).1 h1
  have h3 : Submodule.span C (Set.range B) = Submodule.span C (Set.range (B ∘ b)) := by
    rw [← Submodule.span_span_of_tower O C (Set.range (B ∘ b)), Set.range_comp,
      Submodule.span_image, b.span_eq, Submodule.map_top, LinearMap.coe_range]
  rw [h3, finrank_span_eq_card h2, Fintype.card_fin]

end Algebra

open GlobalTheory.HodgeTateCompare GlobalTheory.EigenLieCompare GlobalTheory.EigenSplit AlgebraicGeometry in

theorem finrank_eigW : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] (Λ : Type) [CommRing Λ] [StarRing Λ] (P : Point p v O Λ), CokernelBound P → P.W = Submodule.span C (Set.range P.bLie) → ∀ τ : Λ →+* O, Module.finrank C (P.eigW τ) = AvDefs.rTau P.Gt P.oGt τ := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ _ Λ _ _ P hcok hW τ
  haveI : IsDomain O := P.integers.hom_inj.isDomain (algebraMap O C)
  haveI : ValuationRing O := ValuationRing.of_integers v P.integers
  haveI : IsFractionRing O C := P.integers.isFractionRing
  haveI := (GlobalTheory.UnitRigidity.smooth_geometricallyConnected_of_isGt _ _ ⟨P.D⟩).1
  obtain ⟨-, -, hb⟩ := Point.omega_free_finite_bijective p C v O Λ P
  have hp : algebraMap O C ((p : O) ^ 2) ≠ 0 := by
    rw [map_pow, map_natCast]
    exact pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  have hinj : Function.Injective P.bLie := by
    intro x y hxy
    have h0 : ∀ t, (P.al₀ t).1 x = (P.al₀ t).1 y := fun t => P.integers.hom_inj (by
      rw [← P.pairV_bLie, ← P.pairV_bLie, hxy])
    have h1 : ∀ z, (P.al z).1 x = (P.al z).1 y := fun z => by
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add z z' hz hz' => simp only [map_add, Submodule.coe_add, Pi.add_apply, hz, hz']
      | tmul c t => simp only [Point.al_tmul, Submodule.coe_smul, Pi.smul_apply, h0]
    refine hb.1 (LinearMap.ext fun f => ?_)
    obtain ⟨z, hz⟩ := hcok f
    have h2 := h1 z
    rw [hz] at h2
    exact mul_left_cancel₀ (fun h => hp (by rw [h, map_zero])) h2
  obtain ⟨h₁, h₂⟩ := finite_free_eigSub P.oGt τ
  let B : eigSub P.oGt τ →ₗ[O] P.V :=
    { toFun := fun x => P.bLie (lieEquiv P.Gt x.1)
      map_add' := fun x y => by
        rw [← P.bLie_add]
        exact congrArg P.bLie (Subtype.ext (lieEquiv_add x.1 y.1))
      map_smul' := fun c x => by
        rw [RingHom.id_apply, ← P.bLie_scale]
        exact congrArg P.bLie (Subtype.ext (lieEquiv_smul c x.1)) }
  have hBi : Function.Injective B := fun x y h =>
    Subtype.ext ((lieEquiv P.Gt).injective (hinj h))
  have hr : Set.range B = P.wRec τ := by
    ext w
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨(eigEquiv P.oGt τ).symm (subEquiv P.oGt τ x), rfl⟩
    · rintro ⟨x, rfl⟩
      refine ⟨(subEquiv P.oGt τ).symm (eigEquiv P.oGt τ x), congrArg P.bLie ?_⟩
      exact (subEquiv_val P.oGt τ _).symm.trans
        (congrArg Subtype.val ((subEquiv P.oGt τ).apply_symm_apply _))
  have hE : P.eigW τ = Submodule.span C (Set.range B) := by
    rw [hr]
    refine le_antisymm ?_ (Submodule.span_le.2 fun w hw => ?_)
    · rintro w ⟨hw, hwτ⟩
      rw [hW] at hw
      obtain ⟨s, hs, x, hx⟩ := exists_smul_mem_of_mem_span (C := C) P.latLie hw
      have hs' : algebraMap O C s ≠ 0 := fun h => hs (P.integers.hom_inj (by rw [h, map_zero]))
      have hxτ : P.bLie x ∈ P.eigV τ := by
        rw [hx, ← algebraMap_smul C s]
        exact Submodule.smul_mem _ _ hwτ
      have hx' : AvDefs.IsEig P.Gt P.oGt τ x := fun a => hinj (by
        rw [P.bLie_act, P.bLie_scale, mem_eigenSub.1 hxτ a, RingHom.comp_apply, algebraMap_smul])
      have : w = (algebraMap O C s)⁻¹ • P.bLie x := by
        rw [hx, ← algebraMap_smul C s, smul_smul, inv_mul_cancel₀ hs', one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨x, hx'⟩, rfl⟩)
    · have h := P.wRec_le τ hw
      refine ⟨?_, h.2⟩
      rw [hW]
      exact Submodule.subset_span h.1
  rw [hE, finrank_span_range B hBi, rTau_eq, eigRank_eq, Module.finrank_linearMap_self]

end GlobalTheory.HodgeTateEigenRank
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbeddingConjugateOscillatorFirst
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff SABMap)
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OneMapRef GlobalTheory.WeilParts GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature GlobalTheory.GalLift GlobalTheory.GalOne

namespace GlobalTheory.GalOne.Facts

theorem infPart_eq_one {D : D7} {v ε} (hε : IsPlaceIdem D v ε) {x : AE D}
    (hx : algebraMap (AF D.host.F) (AE D) ε * (x - 1) = x - 1) : infPart D x = 1 := by
  obtain ⟨α, rfl, -⟩ := hε
  have h3 := congrArg (infPart D) hx
  have h4 : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) = 0 := by
    have e2 : fstA D.host.F (pairA D.host.F 0 α) = 0 := rfl
    have e3 := Algebra.TensorProduct.map_tmul (fstA D.host.F) (AlgHom.id D.host.F D.host.E) (pairA D.host.F 0 α) 1
    rw [e2, TensorProduct.zero_tmul] at e3
    exact e3
  rw [map_mul, h4, zero_mul, map_sub, map_one] at h3
  exact (sub_eq_zero.1 h3.symm)

theorem sigW_add {D : D7} (i : Fin D.R.m) :
    (D.R.sigW ((i : ℕ) + 1)).1 + (D.R.sigW ((i : ℕ) + 1)).2 = (Wc D i).rank := by
  have := D.R.m_add_three_le_k
  have hi := i.2
  rw [rank_Wc i]
  simp only [Ranks.sigW, Ranks.r]
  omega

theorem signs_of_overK {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)
    {σ : D.what₂.LL →+* ℂ} (hσ : OverK σ) (ρ : D.what₂.Tau) (a : Fin (Wc D i).rank) :
    (R.MW i σ).ε ρ a = decide ((a : ℕ) < ((Wc D i).sig (tauE D ρ)).1) := by
  have hs : (Wc D i).sig (tauE D ρ) = D.R.sigW ((i : ℕ) + 1) := D.sp.W_sigval _ (inR i).1 (inR i).2 _
  have he := (R.MW i σ).enum ρ
  unfold Links.parAt at he
  rw [if_pos (((labels_overK σ).1 hσ).2 ρ)] at he
  exact (GlobalTheory.HolDict.isEnum_holPar_kapW _ (rank_Wc i) (by rw [hs]; exact sigW_add i) he a).2

theorem unramAt_conj {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (hR : R.Char F)
    (i : Fin D.R.m) {σ : D.what₂.LL →+* ℂ} {μ' η' : (AE D)ˣ →* Circle} (hμ : ChiAt R i σ μ') (hη : IsEtaConj σ R.eta η')
    {v ε} (hv : NonSplitAt D v ε) : UnramAt ε μ' ∧ UnramAt ε (μ' * η'⁻¹) := by
  have hc := chars_of_lift D G Pl0 T0 A Ks R F hR i
  have u1 : UnramAt ε μ' := fun x a b c => by
    have h0 : R.mu0 ((i : ℕ) + 1) x * R.xi A.μ0 x = 1 := (hc.2.2.2 A.μ0 v ε hv).1 x a b c
    rw [hc.2.1, MonoidHom.one_apply, mul_one] at h0
    exact (hμ.2.2.2.1 x (infPart_eq_one hv.1 a)).elim fun y hy =>
      (circle_eq_one_iff_of_conj D.what₂.embLL σ _ _ y hy.1 hy.2).2 h0
  refine ⟨u1, fun x a b c => ?_⟩
  show μ' x * (η' x)⁻¹ = 1
  rw [u1 x a b c, hη.2.1 x (infPart_eq_one hv.1 a) b c, inv_one, one_mul]

theorem factsAt : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m} (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.Char F → FWTie T R κ v₀ → ∀ (i : Fin D.R.m) (O : OM T R i), Pinned κ v₀ O → ∀ (σ : D.what₂.LL →+* ℂ) (σ' : O.c'.F →+* ℂ), σ'.comp O.jL = σ → OverK σ → FactsAt O σ σ' := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hR tie i O hP σ σ' hσ' hK
  have hin : InR D ((i : ℕ) + 1) := inR i
  have hf : (inC O.c').comp O.jL = D.what₂.embLL := hP.lift.field
  have e0 : res T D.what₂.embLL = T.σ₀ := res_embLL T tie.alg_eq tie.laws.pins.2.2.1
  have hj : ∀ x, O.jL (algebraMap T.Q.c.F D.what₂.LL x) = incF T.Q.c O.c' O.hle x := fun x =>
    (inC O.c').injective ((RingHom.congr_fun hf _).trans (RingHom.congr_fun e0 x))
  have hs : res T σ = sOf O σ' := RingHom.ext fun x =>
    (RingHom.congr_fun hσ' _).symm.trans (congrArg σ' (hj x))
  have hg : GoodEmb T.Q.c (res T σ) := (overK_iff_good T R F κ v₀ hR tie i σ).1 hK
  have hg' : GoodEmb T.Q.c (sOf O σ') := hs ▸ hg
  have hsig : ∀ ρ, (Wc D i).sig (tauE D ρ) = D.R.sigW ((i : ℕ) + 1) := fun ρ => D.sp.W_sigval _ hin.1 hin.2 _
  have hq := (tie.laws.pins.2.2.2 _ hin).2.1
  have hpq : (D.R.sigW ((i : ℕ) + 1)).1 + (T.Q.Dw ((i : ℕ) + 1)).q = (Wc D i).rank := by
    rw [hq]; exact sigW_add i
  have hε : ∀ τ a, (R.MW i σ).ε τ a = decide ((a : ℕ) < (D.R.sigW ((i : ℕ) + 1)).1) := fun τ a => by
    rw [signs_of_overK R i hK τ a, hsig]
  have hl := (labels_overK σ).1 hK
  refine ⟨hs, hg', hg', signs_of_overK R i hK, FactsLat.isONeg_x0Mat _ hpq hε, FactsLat.cart_eq_cartZ _ hpq hε, ?_,
    fun ρ => ?_, fun μ' η' hμ hη => ⟨fun hV => ?_, fun v ε hv => unramAt_conj R F hR i hμ hη hv, ?_⟩⟩
  · have h : IsModelBaseFrameFamily (R.MW i σ) (rank_Wc i) (T.x₀ ((i : ℕ) + 1) (res T σ)) := tie.x0 i σ hg
    rw [hs] at h
    exact h
  · refine Eq.trans ?_ (hl.2 ρ)
    unfold relab labE
    rw [← embV_eq_embF O.c' O.jL hf, ← hσ']
    rfl
  · have h : ChiAt R i σ (T.chiW ((i : ℕ) + 1) (res T σ)) := tie.chiR i σ hg
    rw [hs] at h
    rw [(GlobalTheory.ConjCharUnique.conjChar_unique R F hR i σ).1 _ _ hμ h]
    exact FactsLat.muVal_cast hV (tie.laws.muVal _ hin _ hg')
  · have h := GlobalTheory.EtaConjType.resEta_hasInfExp_of_isEtaConj R F hR i σ hK η' hη
    exact (hypConj_of_chars R F hR i σ hl.1 hl.2).2 μ' η' hμ hη h.1 h.2

end GlobalTheory.GalOne.Facts
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfActsTriviallyAbelianVarietyAlgClosure
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ActTrivialInj

theorem exists_nat_eq_mul {F : Type} [Field F] [NumberField F] {O : Type} [CommRing O] [Algebra O F]
    [IsFractionRing O F] {x : O} (hx : x ≠ 0) : ∃ n : ℕ, n ≠ 0 ∧ ∃ r : O, (n : O) = x * r := by
  set y := algebraMap O F x with hydef
  have hy : y ≠ 0 := by
    intro h
    apply hx
    apply IsFractionRing.injective O F
    rw [map_zero]
    exact h
  have hint : IsIntegral ℚ y := Algebra.IsIntegral.isIntegral y
  have hp0 : (minpoly ℚ y).coeff 0 ≠ 0 := minpoly.coeff_zero_ne_zero hint hy
  set q := IsLocalization.integerNormalization (nonZeroDivisors ℤ) (minpoly ℚ y) with hqdef
  have hq : Polynomial.aeval y q = 0 :=
    IsLocalization.integerNormalization_aeval_eq_zero (nonZeroDivisors ℤ) (minpoly ℚ y) (minpoly.aeval ℚ y)
  obtain ⟨b, hb⟩ := IsLocalization.integerNormalization_map_to_map (nonZeroDivisors ℤ) (minpoly ℚ y)
  set c := q.coeff 0 with hcdef
  have hc : c ≠ 0 := by
    intro h
    have h' := congrArg (fun P => P.coeff 0) hb
    simp only [Polynomial.coeff_map, Polynomial.coeff_smul] at h'
    rw [← hcdef, h, map_zero, eq_comm, smul_eq_zero] at h'
    rcases h' with h' | h'
    · exact nonZeroDivisors.ne_zero b.2 h'
    · exact hp0 h'
  have hO : Polynomial.aeval x q = 0 := by
    apply IsFractionRing.injective O F
    rw [← Polynomial.aeval_algebraMap_apply, map_zero]
    exact hq
  have key := congrArg (Polynomial.aeval x) (Polynomial.X_mul_divX_add q)
  rw [hO, map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C, ← hcdef, algebraMap_int_eq, eq_intCast] at key
  have hc' : (c : O) = x * -(Polynomial.aeval x q.divX) := by linear_combination key
  refine ⟨c.natAbs, Int.natAbs_ne_zero.2 hc, ?_⟩
  have hn : ((c.natAbs : ℕ) : O) = ((|c| : ℤ) : O) := by rw [← Int.natCast_natAbs, Int.cast_natCast]
  rcases abs_choice c with h | h
  · exact ⟨-(Polynomial.aeval x q.divX), by rw [hn, h, hc']⟩
  · exact ⟨Polynomial.aeval x q.divX, by rw [hn, h, Int.cast_neg, hc']; ring⟩

theorem eq_zero_of_act_pullback_eq_one : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosed Ω] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → (∃ d : ℕ, 0 < d ∧ SmoothOfRelativeDimension d A.hom) → ∀ (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 → ∀ (F : Type) [Field F] [NumberField F] (O : Type) [CommRing O] [Algebra O F] [IsFractionRing O F] (α : OAct O A) (x : O), (OAct.pullback (spMap (algebraMap K (AlgebraicClosure Ω))) A α).act x = 1 → x = 0 := by
  rintro K Ω _ _ _ _ A _ _ hA ⟨d, hd, hsm⟩ l _ hl F _ _ O _ _ _ α x hx
  by_contra hx0
  have hl' : l.Prime := Fact.out
  set L := AlgebraicClosure Ω
  set t : Sp L ⟶ Sp K := spMap (algebraMap K L) with htdef
  have hgp := isGrpPullback_pullback A t
  obtain ⟨e, he⟩ := GlobalTheory.exists_mulEquiv_of_isGrpPullback hgp (𝟙 (Sp L)) t (Category.id_comp t).symm
  have h1 : ∀ y : ptOver K L ⟶ A, y ≫ α.act x = 1 := by
    intro y
    obtain ⟨v, rfl⟩ := e.surjective y
    have hv : e (v ≫ (OAct.pullback t A α).act x) = e v ≫ α.act x := by
      apply Over.OverMorphism.ext
      rw [he, Over.comp_left, Over.comp_left, he, Category.assoc, Category.assoc]
      congr 1
      exact pullback.lift_fst _ _ _
    rw [← hv, hx, comp_one, map_one]
  obtain ⟨n, hn0, r, hr⟩ := exists_nat_eq_mul (F := F) hx0
  have h0 : α.act 0 = 1 := by
    have h00 := α.add 0 0
    rw [add_zero] at h00
    exact mul_left_cancel (h00.symm.trans (_root_.mul_one _).symm)
  have hnat : ∀ m : ℕ, ∀ y : ptOver K L ⟶ A, y ≫ α.act (m : O) = y ^ m := by
    intro m y
    induction m with
    | zero => rw [Nat.cast_zero, h0, comp_one, pow_zero]
    | succ m ih => rw [Nat.cast_succ, α.add, comp_mul, ih, α.one, Category.comp_id, pow_succ]
  have hall : ∀ y : ptOver K L ⟶ A, y ^ n = 1 := by
    intro y
    haveI := α.hom r
    rw [← hnat, hr, α.mul, ← Category.assoc, h1, one_comp]
  obtain ⟨v, m, hlm, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn0 l hl'.ne_one
  have hsub : ∀ y : ptOver K L ⟶ A, y ^ (l ^ (v + 1)) = 1 → y ^ (l ^ v) = 1 := by
    intro y hy
    have e1 : (y ^ l ^ v) ^ l = 1 := by rw [← pow_mul, ← pow_succ]; exact hy
    have e2 : (y ^ l ^ v) ^ m = 1 := by rw [← pow_mul, ← hnm]; exact hall y
    have hcop : Nat.Coprime l m := (Nat.Prime.coprime_iff_not_dvd hl').2 hlm
    have e3 := pow_gcd_eq_one.2 ⟨e1, e2⟩
    rwa [hcop.gcd_eq_one, pow_one] at e3
  have hlK : ∀ k : ℕ, ((l ^ k : ℕ) : K) ≠ 0 := fun k => by rw [Nat.cast_pow]; exact pow_ne_zero _ hl
  have cN := GlobalTheory.SepClosedTorsion.card_torsion_sepClosed K L A hA d hsm (l ^ (v + 1)) (hlK _)
  have cv := GlobalTheory.SepClosedTorsion.card_torsion_sepClosed K L A hA d hsm (l ^ v) (hlK _)
  have hfin : Finite {y : ptOver K L ⟶ A // y ^ (l ^ v) = 1} :=
    Nat.finite_of_card_ne_zero (by rw [cv]; exact pow_ne_zero _ (pow_ne_zero _ hl'.ne_zero))
  have hle := Nat.card_le_card_of_injective
    (fun y : {y : ptOver K L ⟶ A // y ^ (l ^ (v + 1)) = 1} =>
      (⟨y.1, hsub y.1 y.2⟩ : {y : ptOver K L ⟶ A // y ^ (l ^ v) = 1}))
    (fun a b h => Subtype.ext (congrArg (fun z : {y : ptOver K L ⟶ A // y ^ (l ^ v) = 1} => z.1) h))
  rw [cN, cv] at hle
  have hlt : (l ^ v) ^ (2 * d) < (l ^ (v + 1)) ^ (2 * d) :=
    Nat.pow_lt_pow_left (Nat.pow_lt_pow_right hl'.one_lt (Nat.lt_succ_self v)) (by omega)
  omega

end GlobalTheory.ActTrivialInj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfDifferentialKernelZeroGermsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_zero_of_differential_kernel_zero_germs : ∀ (R : Type) [CommRing R] (X T X' : Scheme.{0}) (f : X ⟶ Sp R) (M : LB X) (Q : GlobalTheory.AbLaw.Perf f M) (t : T ⟶ Sp R) (φ : X' ⟶ X) (p : X' ⟶ T), IsPullback φ p f t → ∀ e : Fin Q.a → Γ(T, ⊤), (Q.D₀.map (GlobalTheory.FormsLocus.cstT t)).mulVec e = 0 → (∀ (z : X') (i : Q.I), φ z ∈ Q.W i → ∑ k, gs p z ⊤ (e k) * gs φ z (Q.W i) (Q.u k i) = 0) → e = 0 := by
  first | (exact @GlobalTheory.KerGermInj.eq_zero) | (exact GlobalTheory.KerGermInj.eq_zero) | (intros; apply GlobalTheory.KerGermInj.eq_zero  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfForallDual
section
open GlobalTheory GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv GlobalTheory.HTLat Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.HTLat.KerPerp

theorem eq_zero_of_forall_dual {O C M : Type} [CommRing O] [CommRing C] [Algebra O C]
    [AddCommGroup M] [Module O M] [Module.Free O M] (z : C ⊗[O] M)
    (h : ∀ l : Module.Dual O M, (Algebra.linearMap O C ∘ₗ l).liftBaseChange C z = 0) : z = 0 := by
  let b := Module.Free.chooseBasis O M
  refine (b.baseChange C).ext_elem fun i => ?_
  have e : (b.baseChange C).coord i = (Algebra.linearMap O C ∘ₗ b.coord i).liftBaseChange C := by
    refine LinearMap.ext fun w => ?_
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul c m =>
      rw [Module.Basis.coord_apply, Module.Basis.baseChange_repr_tmul,
        LinearMap.liftBaseChange_tmul, LinearMap.comp_apply, Algebra.linearMap_apply,
        Module.Basis.coord_apply, Algebra.smul_def, smul_eq_mul, mul_comm]
  rw [map_zero, Finsupp.zero_apply, ← Module.Basis.coord_apply, e]
  exact h _

theorem mem_W_iff : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C] (Λ : Type) [CommRing Λ] [StarRing Λ] (P : Point p v O Λ), ∀ x : P.V, x ∈ P.W ↔ ∀ y, P.pairV (P.bLie y) x = 0 := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ _ Λ _ _ P x
  obtain ⟨hf, -, hb⟩ := Point.omega_free_finite_bijective p C v O Λ P
  have key : ∀ y (w : P.V), P.pairV (P.bLie y) w =
      (Algebra.linearMap O C ∘ₗ ((LinearMap.proj y : (_ → O) →ₗ[O] O) ∘ₗ
        (omega P.Gt).subtype)).liftBaseChange C (P.alC w) := by
    intro y w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]
    | tmul c t =>
      have e : (c ⊗ₜ[ℤ_[p]] t : P.V) = c • ((1 : C) ⊗ₜ[ℤ_[p]] t) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [Point.alC_tmul, LinearMap.liftBaseChange_tmul, e, map_smul, Point.pairV_bLie]
      rfl
  constructor
  · intro hx y
    rw [key, show P.alC x = 0 from hx, map_zero]
  · intro h
    refine eq_zero_of_forall_dual (P.alC x) fun l => ?_
    obtain ⟨y, rfl⟩ := hb.2 l
    exact (key y x).symm.trans (h y)

end GlobalTheory.HTLat.KerPerp
end

