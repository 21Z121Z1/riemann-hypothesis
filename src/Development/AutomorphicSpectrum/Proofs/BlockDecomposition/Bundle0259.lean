import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0255
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0078
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0002
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0001
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0257
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Coords
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.SubThickRees
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0253
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GreenLabelCharpoly.IrreducibleCharpolyInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0783
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IrrCharEqOneOfSubsingleton
import Development.AbelianVarietyTheory.Counterexamples.SubgroupCharacterSums.SumSubgroupEqZeroIff
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0019
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0016
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0247
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0120
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle0001
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0003
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0256
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
import GroundTheory.PAdicHodge.ExistsGalFixCyclotomicLayerCycloCharNeOne
import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.EmbeddedFrames.PfD
import Formalism.RealPlaceAnalysis.Bundle0001
import Development.WeilBound.CoreStatements.BranchingTraces.HeBranching

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardComapMulCardKerMulCardEq
section
namespace GlobalTheory.CompanionTheory.Counting

theorem card_comap_mul_card_ker_mul_card_eq :
    ∀ (n : ℕ) [NeZero n] (H H' P P' : Type) [AddCommGroup H] [Module (ZMod n) H] [Finite H] [AddCommGroup H'] [Module (ZMod n) H'] [Finite H'] [AddCommGroup P] [Module (ZMod n) P] [Finite P] [AddCommGroup P'] [Module (ZMod n) P'] [Finite P'] (B : P' →ₗ[ZMod n] P →ₗ[ZMod n] ZMod n), Function.Injective B → Function.Injective B.flip → ∀ (loc : H →ₗ[ZMod n] P) (loc' : H' →ₗ[ZMod n] P'), LinearMap.range loc = (⨅ y ∈ LinearMap.range loc', LinearMap.ker (B y)) → ∀ L : Submodule (ZMod n) P, Nat.card ↥(L.comap loc) * Nat.card ↥(LinearMap.ker loc') * Nat.card P = Nat.card ↥((⨅ x ∈ L, LinearMap.ker (B.flip x)).comap loc') * Nat.card H * Nat.card ↥L := by
  intro n _ H H' P P' _ _ _ _ _ _ _ _ _ _ _ _ B hB hB' loc loc' hR L
  have e1 := card_comap_eq_card_ker_mul_card_range_inf (ZMod n) H P loc L
  have e2 := card_comap_eq_card_ker_mul_card_range_inf (ZMod n) H' P' loc'
    (⨅ x ∈ L, LinearMap.ker (B.flip x))
  have e3 := card_eq_card_ker_mul_card_range (ZMod n) H P loc
  have hflip : B.flip.flip = B := LinearMap.flip_flip B
  have hdd := GlobalTheory.T.double_annihilator_eq_self n P' P B.flip hB' (by rw [hflip]; exact hB) (LinearMap.range loc')
  rw [hflip, ← hR] at hdd
  have e4 := GlobalTheory.T.annihilator_intersection_card n P P' B hB hB' (LinearMap.range loc) L
  rw [hdd] at e4
  rw [e1, e2, e3]
  have key : Nat.card ↥(LinearMap.ker loc) * Nat.card ↥(LinearMap.ker loc') *
      (Nat.card P * Nat.card ↥(LinearMap.range loc ⊓ L)) =
      Nat.card ↥(LinearMap.ker loc) * Nat.card ↥(LinearMap.ker loc') *
      (Nat.card ↥(LinearMap.range loc' ⊓ ⨅ x ∈ L, LinearMap.ker (B.flip x)) *
        Nat.card ↥(LinearMap.range loc) * Nat.card ↥L) := by
    rw [e4]
  linarith [key]

end GlobalTheory.CompanionTheory.Counting
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CharacterValuesIntegral
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTPer.IntVal

open Polynomial

variable {l : ℕ} [Fact l.Prime]

theorem isIntegral_of_norm_le_one (z : Om l) (h : ‖z‖ ≤ 1) : IsIntegral ℤ_[l] z := by
  have hz : IsIntegral ℚ_[l] z := Algebra.IsIntegral.isIntegral z
  rw [← PadicAlgCl.spectralNorm_eq] at h
  unfold spectralNorm at h
  rw [spectralValue_le_one_iff (minpoly.monic hz)] at h
  have hlift : minpoly ℚ_[l] z ∈ lifts (algebraMap ℤ_[l] ℚ_[l]) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    exact ⟨⟨_, h n⟩, rfl⟩
  obtain ⟨q, hq, -, hqm⟩ := lifts_and_natDegree_eq_and_monic hlift (minpoly.monic hz)
  refine ⟨q, hqm, ?_⟩
  rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] (Om l), ← eval₂_map, hq, ← aeval_def]
  exact minpoly.aeval ℚ_[l] z

theorem mem_OL_of_norm_le_one (K : FinExt l) (x : ↥K.1) (h : ‖((x : ↥K.1) : Om l)‖ ≤ 1) :
    x ∈ OL K := by
  change x ∈ integralClosure ℤ_[l] ↥K.1
  rw [mem_integralClosure_iff]
  haveI : IsScalarTower ℤ_[l] ↥K.1 (Om l) := IsScalarTower.of_algebraMap_eq fun z => by
    rw [IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] (Om l),
      IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] ↥K.1]
    rfl
  have hinj : Function.Injective (IsScalarTower.toAlgHom ℤ_[l] ↥K.1 (Om l)) :=
    (algebraMap ↥K.1 (Om l)).injective
  exact (isIntegral_algHom_iff _ hinj).1 (isIntegral_of_norm_le_one _ h)

theorem compactSpace_GK (K : FinExt l) : CompactSpace ↥(GK K) := by
  have := K.2
  exact isCompact_iff_compactSpace.mp (IntermediateField.fixingSubgroup_isClosed K.1).isCompact

theorem norm_le_one (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ)
    (hc : Continuous (fun g => (((χ g : (↥K.1)ˣ) : ↥K.1) : Om l))) (g : ↥(GK K)) :
    ‖(((χ g : (↥K.1)ˣ) : ↥K.1) : Om l)‖ ≤ 1 := by
  haveI := compactSpace_GK K
  obtain ⟨M, hM⟩ := (isCompact_range hc).isBounded.exists_norm_le
  have hpow : ∀ n : ℕ, ‖(((χ g : (↥K.1)ˣ) : ↥K.1) : Om l)‖ ^ n ≤ M := fun n => by
    have := hM _ ⟨g ^ n, rfl⟩
    simpa [map_pow, norm_pow] using this
  by_contra h
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt M (not_le.1 h)
  exact absurd (hpow n) (not_le.2 hn)

theorem integral_values {l : ℕ} [Fact l.Prime] (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ) :
    Continuous (fun g => (((χ g : (↥K.1)ˣ) : ↥K.1) : Om l)) →
    ∀ g, ∃ a : ↥(OL K), (a : ↥K.1) = ((χ g : (↥K.1)ˣ) : ↥K.1) := fun hc g =>
  ⟨⟨_, mem_OL_of_norm_le_one K _ (norm_le_one K χ hc g)⟩, rfl⟩

end GlobalTheory.CompanionTheory.LTPer.IntVal
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartBcOfNe
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.Pb

noncomputable section
namespace GlobalTheory.CompanionTheory.ChartBc

theorem chart_bc_of_ne : ∀ {O R R' : Type} [CommRing O] [CommRing R] [CommRing R'] {I : Ideal R} {I' : Ideal R'}
    {γ : DividedPowers I} {γ' : DividedPowers I'} {p : ℕ} {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}
    {κ : O →+* R ⧸ I} {κ' : O →+* R' ⧸ I'} {σ : R →+* R'} (m : NMor γ q κ γ' q κ' σ) (hp : p ≠ 0) (hu : m.u = 𝟙 X) (hg : m.g = RingHom.id O) {V : X.Opens} {d : ℕ}
    (c : Chart γ p q κ V d),
    letI := σ.toAlgebra
    letI := c.D.i.toAlgebra
    ∃ (c' : Chart γ' p q κ' V d) (e : c.D ⟶ (m.mor p).functor.obj c'.D), (∀ i, e.φ (c.t i) = c'.t i) ∧
      (FlatT c.D → FlatT c'.D) ∧
      ∃ f : R' ⊗[R] c.D.B ≃+* c'.D.B, (∀ r, f (r ⊗ₜ 1) = c'.D.i r) ∧ ∀ x, f (1 ⊗ₜ x) = e.φ x := by
  intro O R R' _ _ _ I I' γ γ' p X q κ κ' σ m hp hu hg V d c
  exact chart_bc m hu hg (fun h => absurd h hp) c

end GlobalTheory.CompanionTheory.ChartBc
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartIsGoodStatement
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_is_good : ∀ {O R : Type} [CommRing O] [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}}
    {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} {V : X.Opens} {d : ℕ} (c : Chart γ p q κ V d), c.Good := by
  first | exact @GlobalTheory.CompanionTheory.ChartMaps.good | exact GlobalTheory.CompanionTheory.ChartMaps.good | (intros; apply GlobalTheory.CompanionTheory.ChartMaps.good <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoherentSubobjectCoherent
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.GE

theorem isCoherent_subobject {X : Scheme.{0}} [IsLocallyNoetherian X] {E : X.Modules}
    (hE : IsCoherent E) (D : Subobject E) (hD : (D : X.Modules).IsQuasicoherent) :
    IsCoherent (D : X.Modules) := by
  have hEq := hE.1
  have hC : (cokernel D.arrow).IsQuasicoherent := inferInstance
  have hK : IsCoherent (kernel (cokernel.π D.arrow)) := isCoherent_kernel _ hE
  let e : (D : X.Modules) ≅ kernel (cokernel.π D.arrow) :=
    IsLimit.conePointUniqueUpToIso
      (Abelian.monoIsKernelOfCokernel (f := D.arrow)
        (CokernelCofork.ofπ _ (cokernel.condition D.arrow)) (cokernelIsCokernel _))
      (limit.isLimit _)
  refine ⟨hD, fun U hU => ?_⟩
  have := hK.2 U hU
  let f : Γ(kernel (cokernel.π D.arrow), U) →ₗ[Γ(X, U)] Γ((D : X.Modules), U) :=
    { toFun := e.inv.app U
      map_add' := map_add _
      map_smul' := Scheme.Modules.Hom.app_smul _ }
  exact Module.Finite.of_surjective f (bijective_app_of_iso e.symm U).2

end GlobalTheory.CompanionTheory.GE
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjMemSupp
section
noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.StrongApproxSub

section Group

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E}

abbrev mt (g : HA (AF F) σ J) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E) :=
  ((HA.mat (AF F) σ J g).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E))

theorem mt_mul (g h : HA (AF F) σ J) : mt (g * h) = mt g * mt h := rfl

theorem mt_one : mt (1 : HA (AF F) σ J) = 1 := rfl

theorem mt_inv_mul (g : HA (AF F) σ J) : mt g⁻¹ * mt g = 1 := by
  rw [← mt_mul, inv_mul_cancel, mt_one]

theorem mt_mul_inv (g : HA (AF F) σ J) : mt g * mt g⁻¹ = 1 := by
  rw [← mt_mul, mul_inv_cancel, mt_one]

theorem smul_eq_iff (c : AF F ⊗[F] E) (X : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) :
    (∀ i j, c * X i j = X i j) ↔ c • X = X := by
  constructor
  · intro h
    ext i j
    simpa using h i j
  · intro h i j
    simpa using congrFun (congrFun h i) j

theorem mem_SUSupp {ε : AF F} {g : HA (AF F) σ J} :
    g ∈ SUSupp σ J ε ↔
      g ∈ SUAdelic σ J ∧ algebraMap (AF F) (AF F ⊗[F] E) ε • (mt g - 1) = mt g - 1 :=
  and_congr_right fun _ => smul_eq_iff _ _

def suppGroup (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) (ε : AF F) :
    Subgroup (HA (AF F) σ J) where
  carrier := SUSupp σ J ε
  mul_mem' := by
    intro g h hg hh
    obtain ⟨hg1, hg2⟩ := mem_SUSupp.1 hg
    obtain ⟨hh1, hh2⟩ := mem_SUSupp.1 hh
    refine mem_SUSupp.2 ⟨mul_mem hg1 hh1, ?_⟩
    have e : mt (g * h) - 1 = (mt g - 1) * (mt h - 1) + (mt g - 1) + (mt h - 1) := by
      rw [mt_mul]; noncomm_ring
    rw [e, smul_add, smul_add, ← Matrix.smul_mul, hg2, hh2]
  one_mem' := mem_SUSupp.2 ⟨one_mem _, by rw [mt_one, sub_self, smul_zero]⟩
  inv_mem' := by
    intro g hg
    obtain ⟨hg1, hg2⟩ := mem_SUSupp.1 hg
    refine mem_SUSupp.2 ⟨inv_mem hg1, ?_⟩
    have e : mt g⁻¹ - 1 = -(mt g⁻¹ * (mt g - 1)) := by
      rw [Matrix.mul_sub, mt_inv_mul, Matrix.mul_one]; abel
    rw [e, smul_neg, ← Matrix.mul_smul, hg2]

theorem conj_mem_supp {ε : AF F} {γ h : HA (AF F) σ J} (hγ : γ ∈ SUAdelic σ J)
    (hh : h ∈ SUSupp σ J ε) : γ * h * γ⁻¹ ∈ SUSupp σ J ε := by
  obtain ⟨hh1, hh2⟩ := mem_SUSupp.1 hh
  refine mem_SUSupp.2 ⟨mul_mem (mul_mem hγ hh1) (inv_mem hγ), ?_⟩
  have e : mt (γ * h * γ⁻¹) - 1 = mt γ * (mt h - 1) * mt γ⁻¹ := by
    rw [mt_mul, mt_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, mt_mul_inv]
  rw [e, ← Matrix.smul_mul, ← Matrix.mul_smul, hh2]

def ratSupp (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) (ε : AF F) :
    Subgroup (HA (AF F) σ J) where
  carrier := SASet σ J ε
  mul_mem' := by
    rintro _ _ ⟨γ, hγ, h, hh, rfl⟩ ⟨γ', hγ', h', hh', rfl⟩
    have hc : γ'⁻¹ * h * γ' ∈ SUSupp σ J ε := by
      have := conj_mem_supp (inv_mem (inf_le_left (a := SUAdelic σ J) hγ')) hh
      rwa [inv_inv] at this
    refine ⟨γ * γ', mul_mem hγ hγ', γ'⁻¹ * h * γ' * h', (suppGroup σ J ε).mul_mem hc hh', ?_⟩
    group
  one_mem' := ⟨1, one_mem _, 1, (suppGroup σ J ε).one_mem, by simp⟩
  inv_mem' := by
    rintro _ ⟨γ, hγ, h, hh, rfl⟩
    refine ⟨γ⁻¹, inv_mem hγ, γ * h⁻¹ * γ⁻¹,
      conj_mem_supp (inf_le_left (a := SUAdelic σ J) hγ) ((suppGroup σ J ε).inv_mem hh), ?_⟩
    group

end Group

theorem topGroup {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) : IsTopologicalGroup (HA (AF F) σ J) := by
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  exact inferInstanceAs (IsTopologicalGroup (HR (AF F) σ J))

theorem propSub : Sa2.PropSub := by
  intro F E _ _ _ _ _ σ M J ε
  haveI := topGroup σ J
  exact ⟨(ratSupp σ J ε).topologicalClosure, rfl⟩

end GlobalTheory.CompanionTheory.StrongApproxSub

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalParametrization
section
open ReciprocityTheory.Ty.Fin
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
open Polynomial CategoryTheory

namespace GlobalTheory.CompanionTheory.TyFin

section

variable {K : Type} [Field K] [Fintype K] [DecidableEq K]

theorem isCuspChar_character {d : ℕ} (τ : FDRep ℂ (GL (Fin d) K)) (hs : Simple τ) (hc : IsCuspidal K τ) :
    CuspElliptic.IsCuspChar τ.character := by
  rw [GlobalTheory.CuspCharCheck.isCuspChar_iff]
  refine ⟨τ, hs, rfl, fun a h0 h1 v hv => ?_⟩
  refine hc 2 (twoBlock d a) ?_ le_rfl v fun u hu => hv u ?_
  · intro c
    fin_cases c
    · exact ⟨⟨0, by omega⟩, by simp [twoBlock, h0]⟩
    · exact ⟨⟨a, h1⟩, by simp [twoBlock]⟩
  · intro i j
    by_cases hij : i.val < a ∧ a ≤ j.val
    · exact Or.inr hij
    · left
      by_cases hb : twoBlock d a i = twoBlock d a j
      · exact hu.2 i j hb
      · have hi : a ≤ i.val := by
          by_contra hi
          have hj : j.val < a := by
            by_contra hj
            exact hij ⟨by omega, by omega⟩
          exact hb (by simp [twoBlock, show i.val < a by omega, hj])
        have hj : j.val < a := by
          by_contra hj
          exact hb (by simp [twoBlock, show ¬ i.val < a by omega, show ¬ j.val < a by omega])
        have hne : i ≠ j := fun e => by subst e; omega
        rw [if_neg hne]
        exact hu.1.1 i j (by simp [twoBlock, show ¬ i.val < a by omega, hj])

theorem finrank_of_simple_cuspidal (θ : AlgebraicClosure K →* ℂ)
    (hθ : ∀ x y : AlgebraicClosure K, x ≠ 0 → y ≠ 0 → θ x = θ y → x = y) {d : ℕ} (hd : 1 ≤ d)
    (τ : FDRep ℂ (GL (Fin d) K)) (hs : Simple τ) (hc : IsCuspidal K τ) :
    (Module.finrank ℂ τ : ℤ) = ∏ i ∈ Finset.Ico 1 d, ((q K : ℤ) ^ i - 1) := by
  have h := isCuspChar_character τ hs hc
  obtain ⟨k, -, hk⟩ := GlobalTheory.CuspFormula.exists_regular K θ hθ d hd τ.character
    (GlobalTheory.CuspGL.isIrrChar_of_norm_one _ h.1) (GlobalTheory.CuspGL.isPrimitive_of_isCuspChar _ h)
  have h1 := hk 1
  have hid : Matrix.toLin' ((1 : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 := by
    simp [Module.End.one_eq_id]
  have hfr : Module.finrank K (Fin d → K) = d := by simp
  rw [FDRep.char_one, hid, GlobalTheory.T.invariantSubspaceMobiusInverse_one_prod_Ico K (Fin d → K) (GlobalTheory.CuspGL.rootSum θ k) (GlobalTheory.T.rootPowerSumCharacter_additive_and_X_sub_one_pow K θ k).2
    (by rw [hfr]; omega), hfr, Nat.card_eq_fintype_card] at h1
  have hsign : ((-1 : ℂ)) ^ (d - 1) * ∏ i ∈ Finset.Ico 1 d, (1 - (Fintype.card K : ℂ) ^ i) =
      ∏ i ∈ Finset.Ico 1 d, ((Fintype.card K : ℂ) ^ i - 1) := by
    rw [← Nat.card_Ico 1 d, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun i _ => by ring
  rw [hsign] at h1
  have h2 : ((Module.finrank ℂ τ : ℤ) : ℂ) = ((∏ i ∈ Finset.Ico 1 d, ((q K : ℤ) ^ i - 1) : ℤ) : ℂ) := by
    push_cast
    exact h1
  exact_mod_cast h2

end

end GlobalTheory.CompanionTheory.TyFin
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsActOfHom
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry Polynomial DividedPowers GlobalTheory.LogCris GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.B

namespace GlobalTheory.CompanionTheory.ThickAct

theorem exists_act_of_hom {b : Base} {L : b.Fun} (q : b.Rˣ) (hq : (q : b.R) - 1 ∈ b.I) (D : Thick L)
    {R : Type} [CommRing R] {d : ℕ} (τ : Fin d → Rˣ) (t : Fin d → D.B)
    (g : ∀ T : Thick L, R →+* T.B ⧸ T.J)
    (hcl : ∀ (T : Thick L) (c : D ⟶ T) (k : Fin d), Ideal.Quotient.mk T.J (c.φ (t k)) = g T (τ k))
    (hex : ∀ (T : Thick L) (u : Fin d → T.B), (∀ k, Ideal.Quotient.mk T.J (u k) = g T (τ k)) →
      ∃! c : D ⟶ T, ∀ k, c.φ (t k) = u k) :
    ∃ A : Act (𝟭 _) (thU L q hq) d D, ∀ (T : Thick L) (a : Fin d → (thU L q hq).U T) (c : D ⟶ T) (k : Fin d),
      (A.act a c).φ (t k) = ((a k).1 : T.B) * c.φ (t k) := by
  classical
  have hunit : ∀ (T : Thick L) (x : T.B), IsUnit (Ideal.Quotient.mk T.J x) → IsUnit x := by
    intro T x hx
    obtain ⟨y, hy⟩ := hx.exists_right_inv
    obtain ⟨y', rfl⟩ := Ideal.Quotient.mk_surjective y
    have hm : x * y' - 1 ∈ T.J := by
      rw [← Ideal.Quotient.eq, map_mul, map_one]
      exact hy
    have h1 : IsUnit (1 + (x * y' - 1)) := (GlobalTheory.LogCris.CupModel.isNilpotent_of_mem T hm).isUnit_one_add
    rw [add_sub_cancel] at h1
    exact isUnit_of_mul_isUnit_left h1
  have hker : ∀ (T : Thick L) (x : (thU L q hq).U T), Ideal.Quotient.mk T.J ((x.1 : T.Bˣ) : T.B) = 1 :=
    fun T x => congrArg Units.val (MonoidHom.mem_ker.1 x.2)
  have hlift : ∀ (T : Thick L) (a : Fin d → (thU L q hq).U T) (c : D ⟶ T) (k : Fin d),
      Ideal.Quotient.mk T.J (((a k).1 : T.B) * c.φ (t k)) = g T (τ k) := by
    intro T a c k
    rw [map_mul, hker, one_mul, hcl]
  have hu : ∀ (T : Thick L) (c₁ c₂ : D ⟶ T), (∀ k, c₁.φ (t k) = c₂.φ (t k)) → c₁ = c₂ := by
    intro T c₁ c₂ h
    obtain ⟨c, _, hc⟩ := hex T (fun k => c₂.φ (t k)) (fun k => hcl T c₂ k)
    exact (hc c₁ h).trans (hc c₂ fun _ => rfl).symm
  choose act hact using fun (T : Thick L) (a : Fin d → (thU L q hq).U T) (c : D ⟶ T) =>
    (hex T _ (hlift T a c)).exists
  have hw : ∀ (T : Thick L) (e : D ⟶ T) (k : Fin d), IsUnit (e.φ (t k)) := fun T e k =>
    hunit T _ (by rw [hcl]; exact (τ k).isUnit.map (g T))
  refine ⟨⟨@fun T a c => act T a c, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro T c
    show act T 1 c = c
    apply hu
    intro k
    rw [hact]
    simp
  · intro T a b c
    show act T (a * b) c = act T a (act T b c)
    apply hu
    intro k
    rw [hact, hact, hact]
    exact mul_assoc (((a k).1 : T.Bˣ) : T.B) (((b k).1 : T.Bˣ) : T.B) (c.φ (t k))
  · intro T T' a c φ
    show act T a c ≫ φ = act T' (fun k => (thU L q hq).map φ (a k)) (c ≫ φ)
    apply hu
    intro k
    rw [hact]
    change φ.φ ((act T a c).φ (t k)) = _
    rw [hact, map_mul]
    rfl
  · intro T
    show Nonempty (D ⟶ T)
    choose u hu' using fun k => Ideal.Quotient.mk_surjective (I := T.J) (g T (τ k))
    exact ⟨(hex T u hu').exists.choose⟩
  · intro T
    show ∀ c c' : D ⟶ T, ∃! a, act T a c = c'
    intro c c'
    let a : Fin d → (thU L q hq).U T := fun k =>
      ⟨(hw T c' k).unit * ((hw T c k).unit)⁻¹, by
        rw [MonoidHom.mem_ker, map_mul, map_inv]
        have e : Units.map (Ideal.Quotient.mk T.J).toMonoidHom (hw T c' k).unit =
            Units.map (Ideal.Quotient.mk T.J).toMonoidHom (hw T c k).unit := by
          apply Units.ext
          simp only [Units.coe_map, IsUnit.unit_spec, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, hcl]
        rw [e, mul_inv_cancel]⟩
    refine ⟨a, ?_, ?_⟩
    · apply hu
      intro k
      rw [hact]
      change (((hw T c' k).unit * ((hw T c k).unit)⁻¹ : T.Bˣ) : T.B) * c.φ (t k) = c'.φ (t k)
      rw [Units.val_mul, mul_assoc, IsUnit.val_inv_mul, mul_one, IsUnit.unit_spec]
    · intro a' ha'
      funext k
      apply Subtype.ext
      apply Units.ext
      have h := congrArg (fun e : D ⟶ T => e.φ (t k)) ha'
      simp only [hact] at h
      change ((a' k).1 : T.B) = (((hw T c' k).unit * ((hw T c k).unit)⁻¹ : T.Bˣ) : T.B)
      rw [Units.val_mul, IsUnit.unit_spec (hw T c' k), ← h, mul_assoc, IsUnit.mul_val_inv, mul_one]
  · intro T a c k
    exact hact T a c k

theorem thick_act : ∀ {O : Type} [CommRing O] {F : Fn O} {d : ℕ} (s : F.Small d) {b : Base} (ht : b.t = 1) {κ : O →+* b.R ⧸ b.I} (𝓛 : Lift s.a (fun k => (s.T k : s.R)) b.R b.I κ) (δ : DividedPowers (b.I.map 𝓛.i)) (hδ : IsDPMorphism b.γ δ 𝓛.i) (hp : b.p ≠ 0) (hn : IsNilpotent (b.p : b.R)) (q : b.Rˣ) (hq : (q : b.R) - 1 ∈ b.I), ∃ A : Act (𝟭 _) (thU (F.cr b ht κ) q hq) d (liftObj s ht 𝓛 δ hδ hp hn), ∀ (T : Thick (F.cr b ht κ)) (a : Fin d → (thU (F.cr b ht κ) q hq).U T) (c : liftObj s ht 𝓛 δ hδ hp hn ⟶ T) (k : Fin d), (A.act a c).φ (𝓛.t k) = ((a k).1 : T.B) * c.φ (𝓛.t k) := by
  intro O _ F d s b ht κ 𝓛 δ hδ hp hn q hq
  choose g hg using fun T => GlobalTheory.T.exists_lift_to_thickening s ht 𝓛 δ hδ hp hn T
  exact exists_act_of_hom q hq (liftObj s ht 𝓛 δ hδ hp hn) s.T 𝓛.t g
    (fun T c k => (hg T).1 c (s.T k) (𝓛.t k) (𝓛.hT k).symm) (fun T u hu => (hg T).2.2 u hu)

end GlobalTheory.CompanionTheory.ThickAct
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinitePropagationSpeedHoldsStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_propagation_speed_holds : PositivityTheory.RgBcC.AsmSpeed := by
  first | exact @GlobalTheory.CompanionTheory.WaveSpd.asmSpeed | exact GlobalTheory.CompanionTheory.WaveSpd.asmSpeed | (intros; apply GlobalTheory.CompanionTheory.WaveSpd.asmSpeed <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaloisActionPeriodProduct
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTPer

theorem actB_prod_periods {l : ℕ} [Fact l.Prime] (K : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ)
    (t : (↥K.1 →ₐ[ℚ_[l]] Om l) → Formalism.Per6.BdRp l) (s : Finset (↥K.1 →ₐ[ℚ_[l]] Om l))
    (hs : ∀ μ, μ ∈ s) (ht : ∀ μ, PrePer K χ μ (t μ))
    (g : GQ l) (hg : g ∈ GK K) (hfix : ∀ (μ : ↥K.1 →ₐ[ℚ_[l]] Om l) (x : ↥K.1), g (μ x) = μ x) :
      actB g (∏ μ ∈ s, t μ) =
        algebraMap ℚ_[l] (Formalism.Per6.BdRp l) (Algebra.norm ℚ_[l] ((χ ⟨g, hg⟩ : (↥K.1)ˣ) : ↥K.1)) * ∏ μ ∈ s, t μ := by
  haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  letI : Fintype (↥K.1 →ₐ[ℚ_[l]] Om l) := minpoly.AlgHom.fintype ℚ_[l] (↥K.1) (Om l)
  have hsu : s = Finset.univ := Finset.eq_univ_iff_forall.2 hs
  set y : ↥K.1 := ((χ ⟨g, hg⟩ : (↥K.1)ˣ) : ↥K.1) with hy
  have hn : algebraMap ℚ_[l] (Om l) (Algebra.norm ℚ_[l] y) = ∏ μ ∈ s, μ y := by
    rw [hsu]
    exact Algebra.norm_eq_prod_embeddings ℚ_[l] (Om l) y
  have hr : algebraMap ℚ_[l] (Formalism.Per6.BdRp l) (Algebra.norm ℚ_[l] y) = ∏ μ ∈ s, rB l (μ y) := by
    rw [← map_prod, ← hn]
    exact ((GroundTheory.PAdicHodge.algClToBdR l).commutes _).symm
  rw [map_prod, hr, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun μ _ => (ht μ).2.1 g hg (hfix μ)

end GlobalTheory.CompanionTheory.LTPer
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InterlacingSignatureParityStatement
section
open Finset Matrix PositivityTheory.RgHe.Frame
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.interlacing_signature_parity : ∀ (n : ℕ) (ε : Fin (n + 1) → Bool) (d : Fin (n + 1) → ℝ) (ε' : Fin n → Bool) (d' : Fin n → ℝ) (e : Fin n ⊕ Unit ≃ Fin (n + 1)), PositivityTheory.UnitaryDecomposition.Fits ε ε' e → Function.Injective (Sum.elim d d') → PositivityTheory.UnitaryDecomposition.HeWord ε d ε' d' → (∀ i, (ε i = true ↔ Even (above d d' (d i)))) ∧ ∀ j, (ε' j = true ↔ ¬ Even (above d d' (d' j))) := by
  first | exact @GlobalTheory.CompanionTheory.RgHeFrame.SignWord.heSign | exact GlobalTheory.CompanionTheory.RgHeFrame.SignWord.heSign | (intros; apply GlobalTheory.CompanionTheory.RgHeFrame.SignWord.heSign <;> assumption)
end

