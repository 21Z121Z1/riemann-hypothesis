import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.Bundle0001
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GalOCOkToOC
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0311
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0006
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepUnique
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.PeriodBaseChange.OB
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Bundle0002
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0191
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StdSomeZero
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0312
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0262

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelSystemTransitionIsDPMorphism
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatC

section Gen
variable {W B W' B' : Type} [CommRing W] [CommRing B] [Algebra ℚ B] [CommRing W'] [CommRing B'] [Algebra ℚ B']
  (f : W →+* B) (ξ : W) (f' : W' →+* B') (ξ' : W') (l M : ℕ)

theorem map_isDPMorphism (g : B →+* B') (h : ∀ x ∈ Lat.sub f ξ l M, g x ∈ Lat.sub f' ξ' l M)
    (hg : g (f ξ) = f' ξ')
    (hc : DPClosed (Lat.ι f ξ l M) (Lat.γB f ξ)) (hc' : DPClosed (Lat.ι f' ξ' l M) (Lat.γB f' ξ')) :
    IsDPMorphism (Lat.γ f ξ l M hc) (Lat.γ f' ξ' l M hc') (Lat.map f ξ f' ξ' l M g h) := by
  have hIB : ∀ x ∈ Lat.IB f ξ, g x ∈ Lat.IB f' ξ' := by
    intro x hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    rw [map_mul, hg]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  refine ⟨?_, ?_⟩
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    show Lat.ι f' ξ' l M (Lat.map f ξ f' ξ' l M g h a) ∈ Lat.IB f' ξ'
    rw [Lat.ι_map]
    exact hIB _ ha
  · intro n a ha
    have ha' : Lat.ι f ξ l M a ∈ Lat.IB f ξ := ha
    have hb : Lat.map f ξ f' ξ' l M g h a ∈ Lat.I f' ξ' l M := by
      show Lat.ι f' ξ' l M (Lat.map f ξ f' ξ' l M g h a) ∈ Lat.IB f' ξ'
      rw [Lat.ι_map]
      exact hIB _ ha'
    apply Lat.ι_injective f' ξ' l M
    rw [Lat.ι_γ _ _ _ _ _ hb, Lat.ι_map, Lat.ι_map, Lat.ι_γ _ _ _ _ _ ha, DividedPowers.RatAlgebra.dpow_eq_inv_fact_smul _ _ ha',
      DividedPowers.RatAlgebra.dpow_eq_inv_fact_smul _ _ (hIB _ ha'), map_rat_smul, map_pow]

end Gen

variable {l : ℕ} [Fact l.Prime]

theorem dk_fk (k : ℕ) (w : Ainf l) : dk l k (fk l (k + 1) w) = fk l k w := by
  rfl

theorem levSys_ddp {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (m : ℕ) :
    IsDPMorphism ((levSys h).L (m + 1)).γ ((levSys h).L m).γ ((levSys h).dA m) := by
  exact map_isDPMorphism (fk l (m + 2)) (xi0 l) (fk l (m + 1)) (xi0 l) l M (dk l (m + 1))
    (fun x hx => h.dIn (m + 1) x hx) (dk_fk (m + 1) (xi0 l)) (h.hc (m + 2)) (h.hc (m + 1))

end GlobalTheory.CompanionTheory.LatC
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelToBAlgebraMapField
section
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatC

theorem toB_on_K : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ), ∀ (a : K) (y : (per l K).P), (y : (per l K).B) = (per l K).o a → (lev h k).toB y = algebraMap K (lev h k).B a := by
  intro l _ K M h k a y hy
  have hinj : Function.Injective (algebraMap (BdRp l) (BdR l)) := fun x y h =>
    IsPerfectoidField.algebraMap_bDeRham_injective (K := ℂ_[l]) (p := l) h
  have key : pInv l y = kP l K a := by
    apply hinj
    have h1 : algebraMap (BdRp l) (BdR l) (pInv l y) = y.1 := by
      have := (RingEquiv.ofBijective (algebraMap (BdRp l) (BdR l)).rangeRestrict
        ⟨fun x y h => IsPerfectoidField.algebraMap_bDeRham_injective (K := ℂ_[l]) (p := l) (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩).apply_symm_apply y
      exact congrArg Subtype.val this
    rw [h1]
    exact hy
  show pk l k (pInv l y) = pk l k (kP l K a)
  rw [key]

end GlobalTheory.CompanionTheory.LatC
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelToBEqZeroIffTPowDvd
section
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatC

theorem lev_toB_ker {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ) :
    ∀ x : (per l K).P, (lev h k).toB x = 0 ↔ ∃ y : (per l K).P, (x : (per l K).B) = (per l K).tB ^ k * y := by
  have ht : (per l K).tB = algebraMap (BdRp l) (BdR l) (tBdR l) := by
    change DeRhamPotentiallySemistable.DRPst.iC l (tA l) = _
    change algebraMap (BdRp l) (BdR l) (ACris.iota ℂ_[l] l (tA l)) = _
    rw [show ACris.iota ℂ_[l] l (tA l) = tBdR l from ACris.iota_periodT (untilt_epsilon (p := l))]
  have hinj : Function.Injective (algebraMap (BdRp l) (BdR l)) :=
    IsPerfectoidField.algebraMap_bDeRham_injective (K := ℂ_[l]) (p := l)
  have hp : ∀ x : ↥(algebraMap (BdRp l) (BdR l)).range, algebraMap (BdRp l) (BdR l) (pInv l x) = x := by
    intro x
    obtain ⟨z, hz⟩ := x.2
    have : pInv l x = z := by
      apply (RingEquiv.ofBijective (algebraMap (BdRp l) (BdR l)).rangeRestrict
        ⟨fun x y h => IsPerfectoidField.algebraMap_bDeRham_injective (K := ℂ_[l]) (p := l) (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩).symm_apply_eq.2
      exact Subtype.ext hz.symm
    rw [this, hz]
  intro x
  change pk l k (pInv l x) = 0 ↔ _
  rw [pk, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton']
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨⟨algebraMap (BdRp l) (BdR l) z, z, rfl⟩, ?_⟩
    have := hp x
    rw [← hz, map_mul, map_pow, mul_comm] at this
    rw [ht]
    exact this.symm
  · rintro ⟨y, hy⟩
    obtain ⟨z, hz⟩ := y.2
    refine ⟨z, hinj ?_⟩
    rw [map_mul, map_pow, mul_comm, hp x, hz]
    rw [ht] at hy
    exact hy.symm

end GlobalTheory.CompanionTheory.LatC
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelToBGaloisEquivariant
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatC

theorem pInv_algebraMap (l : ℕ) [Fact l.Prime] (b : BdRp l) (hb : algebraMap (BdRp l) (BdR l) b ∈ (algebraMap (BdRp l) (BdR l)).range) :
    pInv l ⟨algebraMap (BdRp l) (BdR l) b, hb⟩ = b := by
  have : (⟨algebraMap (BdRp l) (BdR l) b, hb⟩ : ↥(algebraMap (BdRp l) (BdR l)).range) = (algebraMap (BdRp l) (BdR l)).rangeRestrict b := rfl
  rw [this]
  exact (RingEquiv.ofBijective (algebraMap (BdRp l) (BdR l)).rangeRestrict
    ⟨fun x y h => IsPerfectoidField.algebraMap_bDeRham_injective (K := ℂ_[l]) (p := l) (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩).symm_apply_apply b

theorem sigmaB_toB {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (k : ℕ) :
    ∀ (g : K.fixingSubgroup) (x y : (per l K).P), (per l K).σ g x = y →
      (lev h k).σB g ((lev h k).toB x) = (lev h k).toB y := by
  rintro g ⟨_, b, rfl⟩ ⟨y, hy⟩ hxy
  have hy' : y = algebraMap (BdRp l) (BdR l) (gP l g b) := by
    refine (Eq.trans hxy.symm ?_)
    exact galBdRField_algebraMap (toBot g.1) b
  subst hy'
  show gB h k g (pk l k (pInv l ⟨_, _⟩)) = pk l k (pInv l ⟨_, _⟩)
  rw [pInv_algebraMap, pInv_algebraMap]
  rfl

end GlobalTheory.CompanionTheory.LatC
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelToBSurjective
section
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatLevels

theorem pInv_surjective (l : ℕ) [Fact l.Prime] : Function.Surjective (pInv l) := by
  intro x
  refine ⟨(algebraMap (BdRp l) (BdR l)).rangeRestrict x, ?_⟩
  unfold pInv
  exact (RingEquiv.ofBijective (algebraMap (BdRp l) (BdR l)).rangeRestrict
    ⟨fun x y h => IsPerfectoidField.algebraMap_bDeRham_injective (K := ℂ_[l]) (p := l)
      (congrArg Subtype.val h), RingHom.rangeRestrict_surjective _⟩).symm_apply_apply x

theorem toB_surjective {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ}
    (h : LevHyp l K M) (k : ℕ) : Function.Surjective (lev h k).toB := by
  have h1 : Function.Surjective ((pk l k).comp (pInv l)) := by
    rw [RingHom.coe_comp]
    exact (Ideal.Quotient.mk_surjective).comp (pInv_surjective l)
  exact h1

end GlobalTheory.CompanionTheory.LatLevels
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelXiMemIdealAndThetaCompat
section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatC.Red

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ}

theorem ι_lam_ainf (h : LevHyp l K M) (k : ℕ) (w : Ainf l) :
    (lev h k).ι ((lev h k).lam (algebraMap (Ainf l) (Acris l) w)) = fk l k w := by
  show pk l k (ACris.iota ℂ_[l] l (algebraMap (Ainf l) (Acris l) w)) = _
  rw [ACris.iota_algebraMap]
  rfl

theorem pk_mem_of_theta (k : ℕ) {d : BdRp l} (hd : IsPerfectoidField.thetaBDeRhamPlusField (K := ℂ_[l]) l d = 0) :
    pk l k d ∈ IB (fk l k) (xi0 l) := by
  have h1 : d ∈ RingHom.ker (IsPerfectoidField.thetaBDeRhamPlusField (K := ℂ_[l]) l) := hd
  rw [IsPerfectoidField.ker_thetaBDeRhamPlusField, ker_thetaBDeRhamPlus ker_theta0,
    Ideal.mem_span_singleton'] at h1
  obtain ⟨c, rfl⟩ := h1
  rw [map_mul]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

theorem xi_and_sub_mem_I (h : LevHyp l K M) (k : ℕ) :
    (lev h k).lam (algebraMap (Ainf l) (Acris l) (xi0 l)) ∈ (lev h k).I ∧
      ∀ (a : OK l K) (w : Ainf l), theta0 l w = okToOC l K a →
        algebraMap (OK l K) (lev h k).A a - (lev h k).lam (algebraMap (Ainf l) (Acris l) w) ∈ (lev h k).I := by
  refine ⟨?_, fun a w hw => ?_⟩
  · show (lev h k).ι _ ∈ IB (fk l k) (xi0 l)
    rw [ι_lam_ainf]
    exact Ideal.mem_span_singleton_self _
  · show (lev h k).ι _ ∈ IB (fk l k) (xi0 l)
    have e : (lev h k).ι (algebraMap (OK l K) (lev h k).A a) = pk l k (kP l K (a : K)) := rfl
    have e2 : (lev h k).ι ((lev h k).lam (algebraMap (Ainf l) (Acris l) w)) =
        pk l k (wittToBDeRhamPlus (normInteger ℂ_[l]) l w) := ι_lam_ainf h k w
    have e3 : (lev h k).ι (algebraMap (OK l K) (lev h k).A a -
        (lev h k).lam (algebraMap (Ainf l) (Acris l) w)) =
        pk l k (kP l K (a : K) - wittToBDeRhamPlus (normInteger ℂ_[l]) l w) := by
      rw [map_sub, e, e2, map_sub]
    rw [e3]
    apply pk_mem_of_theta
    rw [map_sub, IsPerfectoidField.thetaBDeRhamPlusField_wittToBDeRhamPlus, sub_eq_zero]
    have := thetaAlgHom_algClToBdR l (K.val (a : K))
    rw [thetaAlgHom_apply] at this
    refine this.trans ?_
    show _ = ((theta0 l w : OC l) : ℂ_[l])
    rw [hw]
    rfl

end GlobalTheory.CompanionTheory.LatC.Red
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalBinaryGramDensityStatement
section
open PositivityTheory.Rg.Mass
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped TensorProduct ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_binary_gram_density : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
  ∀ (J : Matrix (Fin 2) (Fin 2) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
  (lam : Measure (Fv F v)), IsStdV v lam → ∀ (m : HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin 2 → Fv F v ⊗[F] E)),
  IsGramFib (Fv F v) σ J 1 (coordW (Fv F v) b lam 1 2) (coordHerm (Fv F v) σ b lam 1) m →
  ContinuousOn (fun s : Fv F v => (m (hermScal (Fv F v) σ s) (latV b v)).toReal) {0}ᶜ ∧
  ∫ s, (m (hermScal (Fv F v) σ s) (latV b v)).toReal ∂lam = 1 := by
  first | exact @GlobalTheory.CompanionTheory.SW.StdLat.fibre_masses_standard_lattice | exact GlobalTheory.CompanionTheory.SW.StdLat.fibre_masses_standard_lattice | (intros; apply GlobalTheory.CompanionTheory.SW.StdLat.fibre_masses_standard_lattice <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalGradedClassRepresentativeStatement
section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_graded_class_representative : ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {W : X.Opens} {d : ℕ} (t : Fin d → Γ(X, W)) (s : ℕ) (E : Frame (sP (KS q s {W})) d)
    (ε : Γ(X, W) ≃+* (sP (KS q s {W})).A.obj E.D), IsLoc q s t E ε → ∀ (σ : ∀ T, E.D ⟶ T) (m : ℕ) (r : ℤ), r = m → m + 1 ≤ s →
    (∀ c : HQ (KS q s {W}) r (r + 1) m, ∃ y : Idx m d → Γ(X, W),
      CrystallineSemistableComparison.Pb.Rep (sFil (KS q s {W}) r) (sFil (KS q s {W}) (r + 1)) (fun u => ∑ I : Idx m d, E.form σ I.1 (ε (y I)) u) c) ∧
    ∀ y : Idx m d → Γ(X, W),
      CrystallineSemistableComparison.Pb.Rep (sFil (KS q s {W}) r) (sFil (KS q s {W}) (r + 1)) (fun u => ∑ I : Idx m d, E.form σ I.1 (ε (y I)) u) 0 → y = 0 := by
  first | exact @GlobalTheory.CompanionTheory.ConeLocal.loc_coef | exact GlobalTheory.CompanionTheory.ConeLocal.loc_coef | (intros; apply GlobalTheory.CompanionTheory.ConeLocal.loc_coef <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NilpotentIdentityMorphismCompat
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section
namespace GlobalTheory.CompanionTheory.BcCov

theorem tens_transport {R : Type} [CommRing R] {N : Type} [AddCommGroup N] [Module R N]
    {A B : Type 1} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    {S : Type} [CommRing S] {A' B' : Type 1} [AddCommGroup A'] [Module S A'] [AddCommGroup B'] [Module S B']
    (f : Unit → N → A → A') (f' : Unit → N → B → B') (e : B →ₗ[R] A) (he : Function.Bijective e)
    (e' : B' →ₗ[S] A') (he' : Function.Bijective e') (comm : ∀ i n x, e' (f' i n x) = f i n (e x))
    (H : Tens R (N := fun _ : Unit => N) (M := fun _ => A) (M' := A') f) :
    Tens R (N := fun _ : Unit => N) (M := fun _ => B) (M' := B') f' := by
  obtain ⟨g, hg⟩ := H
  let E : B ≃ₗ[R] A := LinearEquiv.ofBijective e he
  let TE : N ⊗[R] B ≃ₗ[R] N ⊗[R] A := TensorProduct.congr (LinearEquiv.refl R N) E
  let P : (∀ _ : Unit, N ⊗[R] B) ≃+ (∀ _ : Unit, N ⊗[R] A) := AddEquiv.piCongrRight fun _ => TE.toAddEquiv
  let E' : B' ≃+ A' := (LinearEquiv.ofBijective e' he').toAddEquiv
  refine ⟨(P.trans g).trans E'.symm, fun i n x => ?_⟩
  apply E'.injective
  have hP : P (Pi.single i (n ⊗ₜ x)) = Pi.single i (n ⊗ₜ e x) := by
    funext k
    obtain rfl : k = i := Subsingleton.elim _ _
    simp [P, TE, E]
  simp only [AddEquiv.trans_apply, AddEquiv.apply_symm_apply]
  rw [hP, hg]
  exact (comm i n x).symm

section
variable {O R R' : Type} [CommRing O] [CommRing R] [CommRing R'] [Algebra R R'] {I : Ideal R} {I' : Ideal R'}
  {γ : DividedPowers I} {γ' : DividedPowers I'} {p : ℕ} {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}
  {κ : O →+* R ⧸ I} {κ' : O →+* R' ⧸ I'}

theorem pt_obj (m : NMor γ q κ γ' q κ' (algebraMap R R')) (T : Thick (nlFun γ' p X q κ')) :
    pt ((m.mor p).functor.obj T) = pt T ≫ m.u := rfl

theorem inU_obj (m : NMor γ q κ γ' q κ' (algebraMap R R')) (hu : m.u = 𝟙 X) (V : X.Opens)
    (T : Thick (nlFun γ' p X q κ')) (h : InU V T) : InU V ((m.mor p).functor.obj T) := by
  unfold InU at h ⊢
  rw [pt_obj, hu, Category.comp_id]
  exact h

def tmor (m : NMor γ q κ γ' q κ' (algebraMap R R')) (p : ℕ) :
    SMor (thP (nlFun γ p X q κ)) (thP (nlFun γ' p X q κ')) (algebraMap R R') where
  G := (m.mor p).functor
  ρ T := RingHom.id _
  comm _ _ := rfl
  nat _ _ := rfl
  mem _ _ hx := hx
  dp _ _ _ _ := rfl

end

abbrev aT {b : Base} (L : b.Fun) : IdF (thA L) := (thFil L 0).sup (IdF.span _ 0)

abbrev aB {b : Base} (L : b.Fun) : IdF (thA L) := (IdF.bot _).sup (IdF.span _ 0)

theorem aT_top {b : Base} (L : b.Fun) (T : Thick L) : (aT L).S T = ⊤ := by
  have h : (thFil L 0).S T = ⊤ := T.pdPow_zero
  exact top_le_iff.1 (h ▸ le_sup_left)

theorem aB_bot {b : Base} (L : b.Fun) (T : Thick L) : (aB L).S T = ⊥ := by
  change (⊥ : Ideal _) ⊔ Ideal.span {algebraMap b.R _ 0} = ⊥
  simp

theorem mapH_square {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {K L : Cx.{1} R} {L' P : Cx.{1} R'}
    (φ : Cx.Hom K L' σ) (ψ : Cx.Hom L' P (RingHom.id R')) (φ' : Cx.Hom K L (RingHom.id R)) (ψ' : Cx.Hom L P σ) (n : ℕ)
    (h : ∀ z, ψ.f n (φ.f n z) = ψ'.f n (φ'.f n z)) (c : K.H n) : ψ.mapH n (φ.mapH n c) = ψ'.mapH n (φ'.mapH n c) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  exact congrArg (Submodule.Quotient.mk (p := _)) (Subtype.ext (h z.1))

section Gen
variable {R R' : Type} [CommRing R] [CommRing R'] {C C' : Type 1} [Category.{0} C] [Category.{0} C']
  {Φ : PDF R C} {Φ' : PDF R' C'} {σ : R →+* R'}

theorem leC_top (f : SMor Φ Φ' σ) (c : R') (a : IdF Φ.A) (a' : IdF Φ'.A) (h : ∀ T, a'.S T = ⊤) : f.LeC c a a' :=
  fun T _ _ => by rw [h]; trivial

theorem leC_bot (f : SMor Φ Φ' σ) (c : R') (b : IdF Φ.A) (b' : IdF Φ'.A) (h : ∀ T, b.S (f.G.obj T) = ⊥) : f.LeC c b b' := by
  intro T x hx
  rw [h, Ideal.mem_bot] at hx
  subst hx
  rw [map_zero, mul_zero]
  exact Ideal.zero_mem _

theorem sqC_add (f : SMor Φ Φ' σ) {a b : IdF Φ.A} {a' b' : IdF Φ'.A} (c c' : R') (ha : f.LeC c a a') (hb : f.LeC c b b')
    (ha' : f.LeC c' a a') (hb' : f.LeC c' b b') (ha'' : f.LeC (c + c') a a') (hb'' : f.LeC (c + c') b b') (T : C')
    (x : (sq a b).obj (f.G.obj T)) :
    (f.sqC (c + c') ha'' hb'').τ T x = (f.sqC c ha hb).τ T x + (f.sqC c' ha' hb').τ T x := by
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine Subtype.ext ?_
  change Ideal.Quotient.mk _ (algebraMap R' _ (c + c') * f.ρ T y) =
    Ideal.Quotient.mk _ (algebraMap R' _ c * f.ρ T y) + Ideal.Quotient.mk _ (algebraMap R' _ c' * f.ρ T y)
  rw [map_add, add_mul, map_add]

theorem sq_val (f : SMor Φ Φ' σ) {a b : IdF Φ.A} {a' b' : IdF Φ'.A} (ha : f.Le a a') (hb : f.Le b b') (T : C')
    (v : sqM a b (f.G.obj T)) :
    (show sqM a' b' T from (f.sq ha hb).τ T v).1 = Ideal.quotientMap (b'.S T) (f.ρ T) (fun y hy => hb T y hy) v.1 := rfl

theorem sqC_val (f : SMor Φ Φ' σ) {a b : IdF Φ.A} {a' b' : IdF Φ'.A} (c : R') (ha : f.LeC c a a') (hb : f.LeC c b b') (T : C')
    (v : sqM a b (f.G.obj T)) : (show sqM a' b' T from (f.sqC c ha hb).τ T v).1 = f.qC c hb T v.1 := rfl

end Gen

theorem sqC_smul {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {C C' : Type 1} [Category.{0} C] [Category.{0} C']
    {Φ : PDF R C} {Φ' : PDF R' C'} (f : SMor Φ Φ' (algebraMap R R')) {a b : IdF Φ.A} {a' b' : IdF Φ'.A} (r : R) (c : R')
    (ha : f.LeC c a a') (hb : f.LeC c b b') (ha' : f.LeC (r • c) a a') (hb' : f.LeC (r • c) b b') (T : C')
    (x : (sq a b).obj (f.G.obj T)) :
    (f.sqC (r • c) ha' hb').τ T x = algebraMap R R' r • (f.sqC c ha hb).τ T x := by
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
  refine Subtype.ext ?_
  change Ideal.Quotient.mk _ (algebraMap R' _ (r • c) * f.ρ T y) =
    Ideal.Quotient.mk _ (algebraMap R R' r • (algebraMap R' _ c * f.ρ T y))
  refine congrArg (Ideal.Quotient.mk _) ?_
  rw [Algebra.smul_def r c, map_mul, mul_assoc, Algebra.smul_def (algebraMap R R' r)]

section Sq
variable {O R R' : Type} [CommRing O] [CommRing R] [CommRing R'] [Algebra R R'] {I : Ideal R} {I' : Ideal R'}
  {γ : DividedPowers I} {γ' : DividedPowers I'} {p : ℕ} {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}
  {κ : O →+* R ⧸ I} {κ' : O →+* R' ⧸ I'}

theorem st_obj (m : NMor γ q κ γ' q κ' (algebraMap R R')) (hu : m.u = 𝟙 X) (𝒱 : Set X.Opens)
    (T : Thick (nlFun γ' p X q κ')) (h : St ⊤ 𝒱 T) : St ⊤ 𝒱 ((m.mor p).functor.obj T) := by
  obtain ⟨-, W, hW, hi⟩ := h
  exact ⟨trivial, W, hW, inU_obj m hu W T hi⟩

theorem square_tau (m : NMor γ q κ γ' q κ' (algebraMap R R')) {Q₁ Q₂ : ObjectProperty (Thick (nlFun γ p X q κ))}
    {Q₁' Q₂' : ObjectProperty (Thick (nlFun γ' p X q κ'))} (h : Q₂ ≤ Q₁) (h' : Q₂' ≤ Q₁')
    (k₁ : ∀ T, Q₁' T → Q₁ ((m.mor p).functor.obj T)) (k₂ : ∀ T, Q₂' T → Q₂ ((m.mor p).functor.obj T)) (a : R')
    (ha₁ : (m.smor Q₁ Q₁' k₁).LeC a (oT Q₁) (oT Q₁')) (hb₁ : (m.smor Q₁ Q₁' k₁).LeC a (oB Q₁) (oB Q₁'))
    (ha₂ : (m.smor Q₂ Q₂' k₂).LeC a (oT Q₂) (oT Q₂')) (hb₂ : (m.smor Q₂ Q₂' k₂).LeC a (oB Q₂) (oB Q₂'))
    (T : Q₂'.FullSubcategory) (w : (sq (oT Q₁) (oB Q₁)).obj ((m.smor Q₁ Q₁' k₁).G.obj ((incl h').G.obj T))) :
    ((incl h').sq (incl_std h' (some 0) 0) (incl_std h' none 0)).τ T (((m.smor Q₁ Q₁' k₁).sqC a ha₁ hb₁).τ _ w) =
      ((m.smor Q₂ Q₂' k₂).sqC a ha₂ hb₂).τ T (((incl h).sq (incl_std h (some 0) 0) (incl_std h none 0)).τ _ w) := by
  obtain ⟨w, hw⟩ := w
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective w
  refine Subtype.ext ?_
  refine (sq_val (incl h') _ _ T _).trans ?_
  refine Eq.trans ?_ (sqC_val (m.smor Q₂ Q₂' k₂) a ha₂ hb₂ T _).symm
  rw [sqC_val, sq_val]
  dsimp only
  refine (congrArg (Ideal.quotientMap _ _ _) (SMor.qC_mk (m.smor Q₁ Q₁' k₁) a hb₁ ((incl h').G.obj T) y)).trans ?_
  refine (Ideal.quotientMap_mk).trans ?_
  refine Eq.trans ?_ (congrArg ((m.smor Q₂ Q₂' k₂).qC a hb₂ T) Ideal.quotientMap_mk).symm
  refine Eq.trans ?_ (SMor.qC_mk (m.smor Q₂ Q₂' k₂) a hb₂ T _).symm
  rfl

theorem pull_square (m : NMor γ q κ γ' q κ' (algebraMap R R')) {Q₁ Q₂ : ObjectProperty (Thick (nlFun γ p X q κ))}
    {Q₁' Q₂' : ObjectProperty (Thick (nlFun γ' p X q κ'))} (h : Q₂ ≤ Q₁) (h' : Q₂' ≤ Q₁')
    (k₁ : ∀ T, Q₁' T → Q₁ ((m.mor p).functor.obj T)) (k₂ : ∀ T, Q₂' T → Q₂ ((m.mor p).functor.obj T)) (a : R')
    (ha₁ : (m.smor Q₁ Q₁' k₁).LeC a (oT Q₁) (oT Q₁')) (hb₁ : (m.smor Q₁ Q₁' k₁).LeC a (oB Q₁) (oB Q₁'))
    (ha₂ : (m.smor Q₂ Q₂' k₂).LeC a (oT Q₂) (oT Q₂')) (hb₂ : (m.smor Q₂ Q₂' k₂).LeC a (oB Q₂) (oB Q₂'))
    (j : ℕ) (x : CH.H (sq (oT Q₁) (oB Q₁)) j) :
    ((incl h').sq (incl_std h' (some 0) 0) (incl_std h' none 0)).pull j (((m.smor Q₁ Q₁' k₁).sqC a ha₁ hb₁).pull j x) =
      ((m.smor Q₂ Q₂' k₂).sqC a ha₂ hb₂).pull j (((incl h).sq (incl_std h (some 0) 0) (incl_std h none 0)).pull j x) :=
  mapH_square _ _ _ _ j (fun z => funext fun s => square_tau m h h' k₁ k₂ a ha₁ hb₁ ha₂ hb₂ _ _) x

end Sq

theorem bc_cover : ∀ {O R R' : Type} [CommRing O] [CommRing R] [CommRing R'] [Algebra R R'] [Module.Flat R R'] {I : Ideal R}
    {I' : Ideal R'} {γ : DividedPowers I} {γ' : DividedPowers I'} {p : ℕ} (hp : p ≠ 0) (hn : IsNilpotent (p : R))
    {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} {κ' : O →+* R' ⧸ I'}
    (m : NMor γ q κ γ' q κ' (algebraMap R R')) (hu : m.u = 𝟙 X) (hg : m.g = RingHom.id O) (U : Cov q)
    (Q : ObjectProperty (Thick (nlFun γ p X q κ))) (Q' : ObjectProperty (Thick (nlFun γ' p X q κ')))
    (hQ : Q = St ⊤ {⊤}) (hQ' : Q' = St ⊤ {⊤}) (h : ∀ T, Q' T → Q ((m.mor p).functor.obj T))
    (ha : ∀ a : R', (m.smor Q Q' h).LeC a (oT Q) (oT Q')) (hb : ∀ a : R', (m.smor Q Q' h).LeC a (oB Q) (oB Q')) (j : ℕ),
    Tens R (N := fun _ : Unit => R') (M := fun _ => CH.H (sq (oT Q) (oB Q)) j) (M' := CH.H (sq (oT Q') (oB Q')) j)
      fun _ a x => ((m.smor Q Q' h).sqC a (ha a) (hb a)).pull j x := by
  intro O R R' _ _ _ _ _ I I' γ γ' p hp hn X q κ κ' m hu hg U Q Q' hQ hQ' h ha hb j
  subst hQ hQ'
  have hA : ∀ a : R', (tmor m p).LeC a (aT _) (aT _) := fun a => leC_top _ a _ _ (aT_top _)
  have hB : ∀ a : R', (tmor m p).LeC a (aB _) (aB _) := fun a => leC_bot _ a _ _ fun T => aB_bot _ _
  have A : ∀ (𝒱 : Set X.Opens) (k : ∀ T, St (γ := γ') (p := p) (q := q) (κ := κ') ⊤ 𝒱 T → St (γ := γ) (p := p) (q := q) (κ := κ) ⊤ 𝒱 ((m.mor p).functor.obj T)) (a : R'),
      (m.smor _ _ k).LeC a (oT _) (oT _) := fun 𝒱 k a => leC_top _ a _ _ fun T => aT_top _ T.obj
  have B : ∀ (𝒱 : Set X.Opens) (k : ∀ T, St (γ := γ') (p := p) (q := q) (κ := κ') ⊤ 𝒱 T → St (γ := γ) (p := p) (q := q) (κ := κ) ⊤ 𝒱 ((m.mor p).functor.obj T)) (a : R'),
      (m.smor _ _ k).LeC a (oB _) (oB _) := fun 𝒱 k a => leC_bot _ a _ _ fun T => aB_bot _ _
  have Hg : Tens R (N := fun _ : Unit => R')
      (M := fun _ => CH.H (sq (oT (St (γ := γ) (p := p) (q := q) (κ := κ) ⊤ (Set.range U.U))) (oB (St ⊤ (Set.range U.U)))) j)
      (M' := CH.H (sq (oT (St (γ := γ') (p := p) (q := q) (κ := κ') ⊤ (Set.range U.U))) (oB (St ⊤ (Set.range U.U)))) j)
      fun _ a x => ((m.smor _ _ (st_obj m hu _)).sqC a (A _ (st_obj m hu _) a) (B _ (st_obj m hu _) a)).pull j x := by
    refine GlobalTheory.T.stable_cover_cech_vanishing.2.2 (m.mor p).functor (fun _ : Unit => R') (fun _ => sq (aT _) (aB _)) (sq (aT _) (aB _))
      (fun _ a T => ((tmor m p).sqC a (hA a) (hB a)).τ T) (fun _ a _ _ φ x => ((tmor m p).sqC a (hA a) (hB a)).nat φ x)
      (fun _ a a' T x => sqC_add (tmor m p) a a' (hA a) (hB a) (hA a') (hB a') (hA _) (hB _) T x) (fun _ r a T x => sqC_smul (tmor m p) r a (hA a) (hB a) (hA _) (hB _) T x)
      ⊤ ⊤ U.U U.U (fun _ => st_obj m hu _) (fun _ => st_obj m hu _) (st_obj m hu _) ?_ j
    intro S hS j
    obtain ⟨α, hα⟩ := id hS
    obtain ⟨c', -⟩ := coord_res (U.c α) (iInf₂_le α hα) (U.inter S hS)
    exact GlobalTheory.CompanionTheory.ChartLocBc.local_bc hp hn m hu hg c' _ _ rfl rfl (st_obj m hu _) (A _ _) (B _ _) j
  have h₁ : St (γ := γ) (p := p) (q := q) (κ := κ) ⊤ (Set.range U.U) ≤ St ⊤ {⊤} := fun T _ => ⟨trivial, ⊤, rfl, fun _ _ => trivial⟩
  have h₂ : St (γ := γ') (p := p) (q := q) (κ := κ') ⊤ (Set.range U.U) ≤ St ⊤ {⊤} := fun T _ => ⟨trivial, ⊤, rfl, fun _ _ => trivial⟩
  have hc : ∀ W ∈ ({⊤} : Set X.Opens), W ≤ sSup (Set.range U.U) := by
    rintro W rfl
    rw [sSup_range, U.cover]
  have b₁ := (zar (γ := γ) (p := p) (q := q) (κ := κ) ⊤ (Or.inr ⟨hp, Or.inl rfl⟩) _ _ h₁ hc j).2.1 (some 0) none 0 0
  have b₂ := (zar (γ := γ') (p := p) (q := q) (κ := κ') ⊤ (Or.inr ⟨hp, Or.inl rfl⟩) _ _ h₂ hc j).2.1 (some 0) none 0 0
  exact tens_transport _ _ _ b₁ _ b₂
    (fun _ a x => pull_square m h₁ h₂ h (st_obj m hu _) a (ha a) (hb a) (A _ _ a) (B _ _ a) j x) Hg

end GlobalTheory.CompanionTheory.BcCov
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PadicIntMemSub
section
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatCZp

theorem padicInt_mem_sub (l : ℕ) [Fact l.Prime] (M k : ℕ) (z : ℤ_[l]) :
    Lat.pk l k (algClToBdR l (algebraMap ℚ_[l] (PadicAlgCl l) (z : ℚ_[l]))) ∈
      Lat.sub (Lat.fk l k) (xi0 l) l M := by
  have h1 : algClToBdR l (algebraMap ℚ_[l] (PadicAlgCl l) (z : ℚ_[l])) =
      wittToBDeRhamPlus (normInteger ℂ_[l]) l (IsPerfectoidField.padicIntToWitt (K := ℂ_[l]) l z) :=
    ((algClToBdR l).commutes (z : ℚ_[l])).trans
      (IsPerfectoidField.algebraMap_padic_coe (K := ℂ_[l]) l z)
  rw [h1]
  exact Subring.subset_closure (Or.inl ⟨IsPerfectoidField.padicIntToWitt (K := ℂ_[l]) l z, rfl⟩)

end GlobalTheory.CompanionTheory.LatCZp
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProperBirationalClosedSystemStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.proper_birational_closed_system : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] [IsLocallyNoetherian X] (J : X.IdealSheafData) {Z : Scheme.{0}} [Z.Over (Spec (.of A))] (ψ : Z ⟶ J.subscheme), IsProper ψ → (ψ ≫ J.subschemeι) ≫ (X ↘ Spec (.of A)) = (Z ↘ Spec (.of A)) → ∀ (W : J.subscheme.Opens), IsIso (ψ ∣_ W) → ∀ {E : X.Modules}, IsCoherent E → ∀ {S : ℕ → Subobject E}, ClosedSys I E S → (∀ e, Killed J (S e)) → ∀ (B : Subobject ((Scheme.Modules.pullback (ψ ≫ J.subschemeι)).obj E)), (∀ e, B ⊔ powSub I _ (e + 1) = pullSys I (ψ ≫ J.subschemeι) E S e) → ∀ (V : X.affineOpens) (f : Γ(X, V)), J.subschemeι ⁻¹ᵁ X.basicOpen f ≤ W → ∀ x ∈ secs (adjKer (ψ ≫ J.subschemeι) B) V, ∃ k : ℕ, ∀ n, f ^ k • x ∈ secs (S n) V := by
  first | exact @GlobalTheory.CompanionTheory.GE.LocTors.adjKer_pow_smul_mem_secs | exact GlobalTheory.CompanionTheory.GE.LocTors.adjKer_pow_smul_mem_secs | (intros; apply GlobalTheory.CompanionTheory.GE.LocTors.adjKer_pow_smul_mem_secs <;> assumption)
end

