import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0192
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0001
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0003
import GroundTheory.Brauer.BaseChangeCSA

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorTrivialGenericFibreOfStrictHenselClosedFib
section
open IsLocalRing Polynomial

namespace GlobalTheory.LocAcyc

theorem torsorsTrivial_of_ringEquiv {B B' : Type} [CommRing B] [CommRing B'] (e : B ≃+* B')
    (q : ℕ) (h : TorsorsTrivial B' q) : TorsorsTrivial B q := by
  intro D _ _ hfin hproj hff act hbij
  letI : Algebra B' B := e.symm.toRingHom.toAlgebra
  letI : Algebra B' D := ((algebraMap B D).comp e.symm.toRingHom).toAlgebra
  haveI : IsScalarTower B' B D := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hmap : ∀ b : B, algebraMap B D b = algebraMap B' D (e b) := by
    intro b
    change algebraMap B D b = algebraMap B D (e.symm (e b))
    rw [RingEquiv.symm_apply_apply]
  have hsmul : ∀ (b : B) (d : D), b • d = (e b) • d := by
    intro b d
    rw [Algebra.smul_def, Algebra.smul_def, hmap]
  let eL : B ≃ₗ[B'] B' :=
    { e.toAddEquiv with
      map_smul' := fun b' b => by
        change e (e.symm b' * b) = b' * e b
        rw [map_mul, RingEquiv.apply_symm_apply] }
  haveI : Module.FaithfullyFlat B' B := Module.FaithfullyFlat.of_linearEquiv B' B' eL
  haveI : Module.Finite B' B := Module.Finite.equiv eL.symm
  haveI : Module.FaithfullyFlat B D := hff
  haveI : Module.Finite B D := hfin
  have hfin' : Module.Finite B' D := Module.Finite.trans B D
  have hff' : Module.FaithfullyFlat B' D := Module.FaithfullyFlat.trans B' B D
  haveI i1 : RingHomInvPair e.toRingHom e.symm.toRingHom := RingHomInvPair.of_ringEquiv e
  haveI i2 : RingHomInvPair e.symm.toRingHom e.toRingHom := RingHomInvPair.symm _ _
  let sl : D ≃ₛₗ[e.toRingHom] D :=
    { AddEquiv.refl D with
      map_smul' := fun b d => hsmul b d }
  haveI := hproj
  have hproj' : Module.Projective B' D := Module.Projective.of_equiv sl
  let act' : Multiplicative (ZMod q) →* (D ≃ₐ[B'] D) :=
    { toFun := fun g => (act g).restrictScalars B'
      map_one' := by ext x; simp
      map_mul' := fun g g' => by ext x; simp }
  haveI : TensorProduct.CompatibleSMul B' B D D := ⟨fun b m n => by
    rw [hsmul b m, hsmul b n, TensorProduct.smul_tmul]⟩
  let s : TensorProduct B' D D ≃ₗ[B'] TensorProduct B D D :=
    TensorProduct.equivOfCompatibleSMul B B' B' D D
  have hcomp : ∀ x : TensorProduct B' D D,
      Algebra.TensorProduct.productMap
        (Pi.algHom B' (fun _ : Multiplicative (ZMod q) => D) (fun _ => AlgHom.id B' D))
        (Pi.algHom B' (fun _ : Multiplicative (ZMod q) => D) (fun g => (act' g).toAlgHom)) x =
      Algebra.TensorProduct.productMap
        (Pi.algHom B (fun _ : Multiplicative (ZMod q) => D) (fun _ => AlgHom.id B D))
        (Pi.algHom B (fun _ : Multiplicative (ZMod q) => D) (fun g => (act g).toAlgHom)) (s x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b =>
      rfl
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy]
  obtain ⟨σ⟩ := h D hfin' hproj' hff' act' (by
    convert hbij.comp s.bijective using 1
    exact funext hcomp)
  refine ⟨{ toRingHom := (e.symm : B' →+* B).comp σ.toRingHom, commutes' := fun b => ?_ }⟩
  change e.symm (σ (algebraMap B D b)) = b
  rw [hmap, σ.commutes]
  exact e.symm_apply_apply b

end GlobalTheory.LocAcyc

namespace GlobalTheory.LocAcyc

theorem nonempty_genFib_equiv {T T' O : Type} [CommRing T] [IsDomain T] [CommRing T'] [CommRing O]
    [Algebra T T'] [Algebra T O] [Algebra T' O] [IsScalarTower T T' O] (M : Submonoid T)
    (hM : M ≤ nonZeroDivisors T) [IsLocalization M T'] :
    Nonempty (GenFib T O ≃+* GenFib T' O) := by
  haveI : IsDomain T' := IsLocalization.isDomain_of_le_nonZeroDivisors _ hM
  have hinj : Function.Injective (algebraMap T T') := IsLocalization.injective T' hM
  set M1 := Algebra.algebraMapSubmonoid O (nonZeroDivisors T)
  set M2 := Algebra.algebraMapSubmonoid O (nonZeroDivisors T')
  have h1 : M1 ≤ M2 := by
    rintro x ⟨s, hs, rfl⟩
    refine ⟨algebraMap T T' s, ?_, (IsScalarTower.algebraMap_apply T T' O s).symm⟩
    have hs' : s ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hs
    exact mem_nonZeroDivisors_iff_ne_zero.mpr fun h => hs' (hinj (by rw [h, map_zero]))
  have h2 : ∀ x : M2, ∃ m : O, m * x ∈ M1 := by
    rintro ⟨x, y, hy, rfl⟩
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective M y
    refine ⟨algebraMap T O s, a, ?_, ?_⟩
    · have hy' : IsLocalization.mk' T' a s ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hy
      refine mem_nonZeroDivisors_iff_ne_zero.mpr ?_
      rintro rfl
      exact hy' (IsLocalization.mk'_zero s)
    · change algebraMap T O a = algebraMap T O s * algebraMap T' O (IsLocalization.mk' T' a s)
      rw [IsScalarTower.algebraMap_apply T T' O s, ← map_mul, IsLocalization.mk'_spec',
        ← IsScalarTower.algebraMap_apply]
  haveI : IsLocalization M2 (GenFib T O) :=
    IsLocalization.isLocalization_of_is_exists_mul_mem (S := GenFib T O) (M := M1) (N := M2) h1 h2
  exact ⟨(IsLocalization.algEquiv M2 (GenFib T O) (GenFib T' O)).toRingEquiv⟩

end GlobalTheory.LocAcyc

namespace GlobalTheory.LocAcyc

open CategoryTheory in

theorem keyAll_of_keyLocal : KeyLocal → KeyAll := by
  intro hL T O _ _ _ _ _ _ _ hAIC P _ φ hφ hSH q hq hqu
  set p : Ideal T := P.comap (C : T →+* T[X]) with hp
  haveI : p.IsPrime := Ideal.comap_isPrime _ _
  let T' := Localization.AtPrime p
  have hle : p.primeCompl ≤ nonZeroDivisors T := p.primeCompl_le_nonZeroDivisors
  have hAIC' : AbsIntClosed T' :=
    ((absIntClosed_localization_and_quotient T ⟨inferInstance, hAIC⟩).1 p.primeCompl
      (fun h => h (zero_mem p))).2

  have hTO : ∀ a : T, algebraMap T O a = algebraMap T[X] O (C a) := fun a => by
    rw [IsScalarTower.algebraMap_apply T T[X] O, Polynomial.algebraMap_eq]
  have hunit : ∀ s : p.primeCompl, IsUnit (algebraMap T O s) := by
    intro s
    have hs : C (s : T) ∈ P.primeCompl := s.2
    have hu := (IsLocalization.map_units (Localization.AtPrime P)
      (⟨C (s : T), hs⟩ : P.primeCompl)).map φ
    rw [← RingHom.comp_apply, hφ] at hu
    rwa [hTO]
  letI : Algebra T' O := (IsLocalization.lift (M := p.primeCompl) (S := T') hunit).toAlgebra
  haveI : IsScalarTower T T' O :=
    IsScalarTower.of_algebraMap_eq (fun x => (IsLocalization.lift_eq hunit x).symm)
  letI : Algebra T'[X] O := (eval₂RingHom (algebraMap T' O) (algebraMap T[X] O X)).toAlgebra
  haveI : IsScalarTower T' T'[X] O :=
    IsScalarTower.of_algebraMap_eq (fun x => by
      change _ = eval₂ (algebraMap T' O) (algebraMap T[X] O X) (algebraMap T' T'[X] x)
      rw [Polynomial.algebraMap_eq, eval₂_C])

  letI : Algebra T[X] T'[X] := Polynomial.algebra T T'
  haveI : IsLocalization (Submonoid.map C p.primeCompl) T'[X] :=
    Polynomial.isLocalization p.primeCompl T'
  have hdisj : Disjoint (Submonoid.map C p.primeCompl : Set T[X]) (P : Set T[X]) := by
    rw [Set.disjoint_left]
    rintro _ ⟨s, hs, rfl⟩ hsP
    exact hs hsP
  set P' : Ideal T'[X] := P.map (algebraMap T[X] T'[X]) with hP'
  haveI hP'prime : P'.IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint _ T'[X] P inferInstance hdisj
  have hcomapP' : P'.comap (algebraMap T[X] T'[X]) = P :=
    IsLocalization.comap_map_of_isPrime_disjoint _ T'[X] inferInstance hdisj
  have hCcomm : ∀ a : T, C (algebraMap T T' a) = algebraMap T[X] T'[X] (C a) := fun a => by
    change _ = (C a).map (algebraMap T T')
    rw [Polynomial.map_C]
  have hmax : P'.comap (C : T' →+* T'[X]) = maximalIdeal T' := by
    rw [← IsLocalization.map_comap p.primeCompl T' (P'.comap C),
      ← IsLocalization.map_comap p.primeCompl T' (maximalIdeal T'),
      IsLocalization.AtPrime.comap_maximalIdeal T' p]
    congr 1
    ext a
    change C (algebraMap T T' a) ∈ P' ↔ C a ∈ P
    rw [hCcomm, ← Ideal.mem_comap, hcomapP']

  haveI : IsLocalization.AtPrime (Localization.AtPrime P') P := by
    have := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Submonoid.map C p.primeCompl) (Localization.AtPrime P') P'
    have hc : (P'.comap (algebraMap T[X] T'[X])).primeCompl = P.primeCompl := by
      ext x; simp only [Ideal.mem_primeCompl_iff, hcomapP']
    unfold IsLocalization.AtPrime at this ⊢
    rw [hc] at this
    exact this
  let e : Localization.AtPrime P ≃ₐ[T[X]] Localization.AtPrime P' :=
    IsLocalization.algEquiv P.primeCompl _ _
  let φ' : Localization.AtPrime P' →+* O := φ.comp e.symm.toRingEquiv.toRingHom
  have hOO : (algebraMap T'[X] O).comp (algebraMap T[X] T'[X]) = algebraMap T[X] O := by
    refine Polynomial.ringHom_ext (fun a => ?_) ?_
    · change eval₂ (algebraMap T' O) (algebraMap T[X] O X) ((C a).map (algebraMap T T')) = _
      rw [Polynomial.map_C, eval₂_C, ← IsScalarTower.algebraMap_apply, hTO]
    · change eval₂ (algebraMap T' O) (algebraMap T[X] O X) ((X : T[X]).map (algebraMap T T')) = _
      rw [Polynomial.map_X, eval₂_X]
  have hφ' : φ'.comp (algebraMap T'[X] (Localization.AtPrime P')) = algebraMap T'[X] O := by
    refine IsLocalization.ringHom_ext (Submonoid.map C p.primeCompl) ?_
    rw [RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq, hOO]
    refine RingHom.ext fun f => ?_
    change φ (e.symm (algebraMap T[X] _ f)) = _
    rw [AlgEquiv.commutes, ← RingHom.comp_apply, hφ]
  have hSH' : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ' := by
    obtain ⟨h1, h2, h3, h4⟩ := hSH
    refine ⟨h1, h2, ?_, ?_⟩
    · refine ⟨fun a ha => ?_⟩
      change IsUnit (φ (e.symm a)) at ha
      have h5 : IsUnit (e.symm a) := h3.map_nonunit _ ha
      simpa using h5.map e
    · haveI : (RingHom.toMorphismProperty @RingHom.Etale).RespectsIso :=
        RingHom.toMorphismProperty_respectsIso_iff.mp RingHom.Etale.respectsIso
      unfold GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale at h4 ⊢
      rw [CommRingCat.ofHom_comp]
      haveI : IsIso (CommRingCat.ofHom e.symm.toRingEquiv.toRingHom) :=
        inferInstanceAs (IsIso (e.symm.toRingEquiv.toCommRingCatIso).hom)
      exact (MorphismProperty.cancel_left_of_respectsIso _ _ _).mpr h4
  have hqu' : IsUnit (q : T') := by
    simpa using hqu.map (algebraMap T T')
  have key := hL T' O hAIC' P' φ' hφ' hSH' hmax trivial q hq hqu'
  obtain ⟨eG⟩ := nonempty_genFib_equiv (T := T) (T' := T') (O := O) p.primeCompl hle
  exact torsorsTrivial_of_ringEquiv eG q key

end GlobalTheory.LocAcyc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceEqSumEigenMultiplicities
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

theorem trace_eq_sum_eigenspaces : ∀ (C : Type) [Field C] (O : Type) [CommRing O] [Algebra O C] (Λ : Type) [CommRing Λ] (h : ℕ) (ρ : Λ → Matrix (Fin h) (Fin h) O), iSupIndep (fun σ : Λ →+* O => eig C ρ σ) → (⨆ σ : Λ →+* O, eig C ρ σ) = ⊤ → {σ : Λ →+* O | eig C ρ σ ≠ ⊥}.Finite ∧ ∀ S : Finset (Λ →+* O), (∀ σ, eig C ρ σ ≠ ⊥ → σ ∈ S) → ∀ a : Λ, algebraMap O C (ρ a).trace = ∑ σ ∈ S, (Module.finrank C (eig C ρ σ) : C) * algebraMap O C (σ a) := by
  classical
  intro C _ O _ _ Λ _ h ρ hind htop
  have hfin : {σ : Λ →+* O | eig C ρ σ ≠ ⊥}.Finite :=
    WellFoundedGT.finite_ne_bot_of_iSupIndep hind
  refine ⟨hfin, fun S hS a => ?_⟩
  set f : (Fin h → C) →ₗ[C] (Fin h → C) := Matrix.toLin' ((ρ a).map (algebraMap O C)) with hf
  have hact : ∀ (σ : Λ →+* O) (x : Fin h → C), x ∈ eig C ρ σ → f x = algebraMap O C (σ a) • x := by
    intro σ x hx
    have h1 := (Submodule.mem_iInf _).1 hx a
    exact Module.End.mem_eigenspace_iff.1 h1
  have hmaps : ∀ σ : Λ →+* O, Set.MapsTo f (eig C ρ σ) (eig C ρ σ) := by
    intro σ x hx
    have hx' : x ∈ eig C ρ σ := hx
    show f x ∈ eig C ρ σ
    rw [hact σ x hx']
    exact Submodule.smul_mem _ _ hx'
  have hint : DirectSum.IsInternal (fun σ : Λ →+* O => eig C ρ σ) :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind htop
  have htr := LinearMap.trace_eq_sum_trace_restrict' hint hfin hmaps
  have hrestrict : ∀ σ : Λ →+* O, LinearMap.trace C (eig C ρ σ) (f.restrict (hmaps σ))
      = (Module.finrank C (eig C ρ σ) : C) * algebraMap O C (σ a) := by
    intro σ
    have : f.restrict (hmaps σ) = algebraMap O C (σ a) • LinearMap.id := by
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      show f x.1 = algebraMap O C (σ a) • x.1
      exact hact σ x.1 x.2
    rw [this, map_smul, LinearMap.trace_id, smul_eq_mul, mul_comm]
  have hleft : algebraMap O C (ρ a).trace = LinearMap.trace C (Fin h → C) f := by
    rw [hf, Matrix.trace_toLin'_eq, Matrix.trace, Matrix.trace, map_sum]
    rfl
  rw [hleft, htr]
  simp only [hrestrict]
  refine Finset.sum_subset (fun σ hσ => hS σ (by simpa using hσ)) ?_
  intro σ _ hσ
  have hbot : eig C ρ σ = ⊥ := by
    by_contra hne
    exact hσ (by simpa using hne)
  rw [hbot]
  simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceLsmulEqFinrankMulTrace
section
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps

namespace GlobalTheory

theorem trace_lsmul_free_eq_finrank_mul_trace (R Λ M : Type) [CommRing R] [Nontrivial R] [CommRing Λ] [Nontrivial Λ] [Algebra R Λ] [Module.Free R Λ] [Module.Finite R Λ] [AddCommGroup M] [Module R M] [Module Λ M] [IsScalarTower R Λ M] [Module.Free Λ M] [Module.Finite Λ M] (a : Λ) :
    LinearMap.trace R M (Algebra.lsmul R R M a) = (Module.finrank Λ M : R) * Algebra.trace R Λ a := by
  classical
  let b := Module.Free.chooseBasis R Λ
  let e := Module.Free.chooseBasis Λ M
  rw [LinearMap.trace_eq_matrix_trace R (b.smulTower e), Algebra.trace_eq_matrix_trace b,
    Module.finrank_eq_card_chooseBasisIndex]
  simp only [Matrix.trace, Matrix.diag, Fintype.sum_prod_type, LinearMap.toMatrix_apply,
    Module.Basis.smulTower_apply, Module.Basis.smulTower_repr, Algebra.leftMulMatrix_eq_repr_mul]
  have h : ∀ i k, (b.repr ((e.repr (((Algebra.lsmul R R M) a) (b i • e k))) k)) i = (b.repr (a * b i)) i := by
    intro i k
    show (b.repr ((e.repr (a • (b i • e k))) k)) i = _
    rw [smul_smul, LinearEquiv.map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul, mul_one]
  simp only [h]
  rw [Finset.sum_comm, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceRestrictScalarsField
section
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.QTrace

set_option autoImplicit false in
private lemma trace_restrictScalars_rat {F W : Type} [Field F] [NumberField F] [AddCommGroup W]
    [Module F W] [Module ℚ W] [IsScalarTower ℚ F W] [FiniteDimensional F W] (f : W →ₗ[F] W) :
    LinearMap.trace ℚ W (f.restrictScalars ℚ) = Algebra.trace ℚ F (LinearMap.trace F W f) := by
  classical
  let b := Module.finBasis ℚ F
  let d := Module.finBasis F W
  rw [LinearMap.trace_eq_matrix_trace ℚ (b.smulTower d), LinearMap.trace_eq_matrix_trace F d,
    Matrix.trace, Matrix.trace, map_sum, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Algebra.trace_eq_matrix_trace b, Matrix.trace]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [LinearMap.toMatrix_apply, Module.Basis.smulTower_apply, Module.Basis.smulTower_repr,
    Algebra.leftMulMatrix_eq_repr_mul, mul_comm]

set_option autoImplicit false in
private lemma trace_mulLeft_matrix (n : ℕ) (M : Matrix (Fin n) (Fin n) ℂ) :
    LinearMap.trace ℂ (Matrix (Fin n) (Fin n) ℂ) (LinearMap.mulLeft ℂ M) = n * M.trace := by
  rw [LinearMap.trace_eq_matrix_trace ℂ (Matrix.stdBasis ℂ (Fin n) (Fin n))]
  simp only [Matrix.trace, LinearMap.toMatrix_apply, Matrix.diag, Fintype.sum_prod_type]
  have key : ∀ i j, (Matrix.stdBasis ℂ (Fin n) (Fin n)).repr
      (LinearMap.mulLeft ℂ M (Matrix.stdBasis ℂ (Fin n) (Fin n) (i, j))) (i, j) = M i i := by
    intro i j
    rw [Matrix.stdBasis_eq_single]
    simp [Matrix.stdBasis]
  simp only [key]
  simp [Finset.sum_const, Finset.card_univ, Finset.mul_sum]

set_option autoImplicit false in
private lemma embedding_trace_mulLeft_eq_mul_trace {F A : Type} [Field F] [Ring A] [Algebra F A]
    [FiniteDimensional F A] [Algebra.IsCentral F A] [IsSimpleRing A] (n : ℕ)
    (hn : Module.finrank F A = n ^ 2) (σ : F →+* ℂ) (φ : A →+* Matrix (Fin n) (Fin n) ℂ)
    (hφ : ∀ x : F, φ (algebraMap F A x) = Matrix.scalar (Fin n) (σ x)) (c : A) :
    σ (LinearMap.trace F A (LinearMap.mulLeft F c)) = n * (φ c).trace := by
  letI : Algebra F ℂ := σ.toAlgebra
  have hn0 : n ≠ 0 := by
    rintro rfl
    have : 0 < Module.finrank F A := Module.finrank_pos
    simp [hn] at this
  haveI : NeZero n := ⟨hn0⟩
  let φF : A →ₐ[F] Matrix (Fin n) (Fin n) ℂ :=
    { φ with commutes' := fun x => (hφ x).trans rfl }
  let ι : ℂ →ₐ[ℂ] Matrix (Fin n) (Fin n) ℂ := Algebra.ofId ℂ _
  let G : TensorProduct F ℂ A →ₐ[ℂ] Matrix (Fin n) (Fin n) ℂ :=
    Algebra.TensorProduct.lift ι φF (fun z a => Algebra.commute_algebraMap_left z _)
  let H : TensorProduct F A ℂ →ₐ[F] Matrix (Fin n) (Fin n) ℂ :=
    Algebra.TensorProduct.lift φF (ι.restrictScalars F)
      (fun a z => (Algebra.commute_algebraMap_left z _).symm)
  have hH : Function.Injective H := by
    rw [← TwoSidedIdeal.ker_eq_bot]
    by_contra hne
    obtain ⟨b, hb, hmem⟩ := _root_.GroundTheory.Brauer.exists_one_tmul_mem_of_ne_bot _ hne
    rw [TwoSidedIdeal.mem_ker] at hmem
    have : algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ) b = 0 := by
      have h1 : H (1 ⊗ₜ[F] b) = φF 1 * (ι.restrictScalars F) b :=
        Algebra.TensorProduct.lift_tmul _ _ _ _ _
      rw [h1, map_one, one_mul] at hmem
      exact hmem
    exact hb ((algebraMap ℂ (Matrix (Fin n) (Fin n) ℂ)).injective (this.trans (map_zero _).symm))
  have hGH : ∀ x, G x = H (TensorProduct.comm F ℂ A x) := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul z a =>
      rw [TensorProduct.comm_tmul]
      simp only [G, H, Algebra.TensorProduct.lift_tmul, AlgHom.restrictScalars_apply, ι, Algebra.ofId_apply]
      exact Algebra.commutes z _
    | add x y hx hy => simp [map_add, hx, hy]
  have hG : Function.Injective G := by
    intro x y hxy
    rw [hGH, hGH] at hxy
    exact (TensorProduct.comm F ℂ A).injective (hH hxy)
  have hdim : Module.finrank ℂ (TensorProduct F ℂ A) = Module.finrank ℂ (Matrix (Fin n) (Fin n) ℂ) := by
    rw [_root_.GroundTheory.Brauer.finrank_baseChange_eq, hn, Module.finrank_matrix]
    simp [sq]
  haveI : FiniteDimensional ℂ (TensorProduct F ℂ A) :=
    Module.finite_of_finrank_pos (by rw [hdim]; simp [Module.finrank_matrix, Nat.pos_of_ne_zero hn0])
  let e : TensorProduct F ℂ A ≃ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ :=
    LinearEquiv.ofBijective G.toLinearMap
      ⟨hG, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hG⟩
  have hconj : e.conj ((LinearMap.mulLeft F c).baseChange ℂ) = LinearMap.mulLeft ℂ (φ c) := by
    refine LinearMap.ext fun y => ?_
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    show G _ = φ c * G x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul z a =>
      rw [LinearMap.baseChange_tmul]
      simp only [G, Algebra.TensorProduct.lift_tmul, ι, Algebra.ofId_apply, LinearMap.mulLeft_apply]
      show algebraMap ℂ _ z * φ (c * a) = φ c * (algebraMap ℂ _ z * φ a)
      rw [map_mul, ← mul_assoc, ← mul_assoc, Algebra.commutes z (φ c)]
    | add x y hx hy => simp [map_add, hx, hy, mul_add]
  rw [← trace_mulLeft_matrix, ← hconj, LinearMap.trace_conj', LinearMap.trace_baseChange]
  rfl

set_option autoImplicit false in
private lemma trace_pi_comp_proj {N : Type} [AddCommGroup N] [Module ℚ N] [FiniteDimensional ℚ N] (m : ℕ)
    (f : N →ₗ[ℚ] N) :
    LinearMap.trace ℚ (Fin m → N) (LinearMap.pi fun i => f ∘ₗ LinearMap.proj i) =
      m * LinearMap.trace ℚ N f := by
  let e := TensorProduct.piScalarRight ℚ ℚ N (Fin m)
  have h : e.symm.conj (LinearMap.pi fun i => f ∘ₗ LinearMap.proj i) = TensorProduct.map f LinearMap.id := by
    apply TensorProduct.ext'
    intro x y
    have hx : (LinearMap.pi fun i => f ∘ₗ LinearMap.proj i) (e (x ⊗ₜ y)) = e (f x ⊗ₜ y) := by
      ext i
      simp [e, TensorProduct.piScalarRight_apply]
    simp only [LinearEquiv.conj_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_symm, hx,
      LinearEquiv.symm_apply_apply, TensorProduct.map_tmul, LinearMap.id_apply]
  rw [← LinearMap.trace_conj' _ e.symm, h, LinearMap.trace_tensorProduct', LinearMap.trace_id]
  simp [mul_comm]

set_option autoImplicit false in
private lemma trace_and_finrank_of_linearEquiv_pi {A M S : Type} [Ring A] [Algebra ℚ A] [AddCommGroup M]
    [Module A M] [Module ℚ M] [IsScalarTower ℚ A M] [AddCommGroup S] [Module A S] [Module ℚ S]
    [IsScalarTower ℚ A S] [FiniteDimensional ℚ S] (k : ℕ) (e : M ≃ₗ[A] (Fin k → S)) (c : A) :
    LinearMap.trace ℚ M (DistribMulAction.toLinearMap ℚ M c) =
        k * LinearMap.trace ℚ S (DistribMulAction.toLinearMap ℚ S c) ∧
      Module.finrank ℚ M = k * Module.finrank ℚ S := by
  let e' : M ≃ₗ[ℚ] (Fin k → S) := e.restrictScalars ℚ
  refine ⟨?_, ?_⟩
  · rw [← LinearMap.trace_conj' _ e', ← trace_pi_comp_proj]
    congr 1
    refine LinearMap.ext fun v => funext fun x => ?_
    show e (c • e.symm v) x = c • v x
    rw [map_smul, LinearEquiv.apply_symm_apply]
    rfl
  · rw [e'.finrank_eq, Module.finrank_pi_fintype]
    simp

set_option autoImplicit false in
private lemma trace_mul_finrank_eq_finrank_mul_trace {A M : Type} [Ring A] [Algebra ℚ A] [FiniteDimensional ℚ A]
    [IsSimpleRing A] [AddCommGroup M] [Module A M] [Module ℚ M] [IsScalarTower ℚ A M]
    [FiniteDimensional ℚ M] (c : A) :
    LinearMap.trace ℚ M (DistribMulAction.toLinearMap ℚ M c) * Module.finrank ℚ A =
      Module.finrank ℚ M * LinearMap.trace ℚ A (DistribMulAction.toLinearMap ℚ A c) := by
  haveI : IsArtinianRing A := IsArtinianRing.of_finite ℚ A
  haveI : IsSemisimpleRing A := (IsSimpleRing.isSemisimpleRing_iff_isArtinianRing (R := A)).mpr inferInstance
  haveI : Module.Finite A M := Module.Finite.of_restrictScalars_finite ℚ A M
  obtain ⟨S, hS⟩ := IsSemisimpleModule.exists_simple_submodule A (A × M)
  have hP : IsIsotypicOfType A (A × M) S := IsSimpleRing.isIsotypic A (A × M) S
  have hA : IsIsotypicOfType A A S := by
    refine (LinearEquiv.isIsotypicOfType_iff
      (LinearEquiv.ofInjective (LinearMap.inl A A M) LinearMap.inl_injective)).mpr ?_
    refine isIsotypicOfType_submodule_iff.mpr ?_
    intro m _ _
    exact hP m
  have hM : IsIsotypicOfType A M S := by
    refine (LinearEquiv.isIsotypicOfType_iff
      (LinearEquiv.ofInjective (LinearMap.inr A A M) LinearMap.inr_injective)).mpr ?_
    refine isIsotypicOfType_submodule_iff.mpr ?_
    intro m _ _
    exact hP m
  haveI : FiniteDimensional ℚ S :=
    Module.Finite.of_injective ((S.subtype).restrictScalars ℚ) S.injective_subtype
  obtain ⟨k, ⟨eA⟩⟩ := hA.linearEquiv_fun
  obtain ⟨m, ⟨eM⟩⟩ := hM.linearEquiv_fun
  obtain ⟨hA1, hA2⟩ := trace_and_finrank_of_linearEquiv_pi k eA c
  obtain ⟨hM1, hM2⟩ := trace_and_finrank_of_linearEquiv_pi m eM c
  rw [hA1, hA2, hM1, hM2]
  push_cast
  ring

set_option autoImplicit false in

theorem _root_.GlobalTheory.QTrace.q_trace : ∀ {F A V : Type} [Field F] [NumberField F] [Ring A] [Algebra F A] [FiniteDimensional F A] [Algebra.IsCentral F A]
    [IsSimpleRing A] [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V] (n : ℕ), Module.finrank F A = n ^ 2 →
    ∀ (ρ : A →+* Module.End ℚ V) (ψ : (F →+* ℂ) → (A →+* Matrix (Fin n) (Fin n) ℂ)),
    (∀ σ (x : F), ψ σ (algebraMap F A x) = Matrix.scalar (Fin n) (σ x)) → ∀ c : A,
    ((n * Module.finrank ℚ F : ℕ) : ℂ) * ((LinearMap.trace ℚ V (ρ c) : ℚ) : ℂ) =
      (Module.finrank ℚ V : ℂ) * ∑ σ, Matrix.trace (ψ σ c) := by
  intro F A V _ _ _ _ _ _ _ _ _ _ n hn ρ ψ hψ c
  have hn0 : n ≠ 0 := by
    rintro rfl
    have : 0 < Module.finrank F A := Module.finrank_pos
    simp [hn] at this
  letI : Algebra ℚ A := RingHom.toAlgebra' ((algebraMap F A).comp (algebraMap ℚ F))
    (fun q x => Algebra.commutes _ x)
  haveI : IsScalarTower ℚ F A := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : FiniteDimensional ℚ A := Module.Finite.trans F A
  letI : Module A V := Module.compHom V ρ
  have hρq : ∀ q : ℚ, ρ (algebraMap ℚ A q) = algebraMap ℚ (Module.End ℚ V) q := fun q =>
    congrArg (fun f : ℚ →+* Module.End ℚ V => f q)
      (RingHom.ext_rat (ρ.comp (algebraMap ℚ A)) (algebraMap ℚ (Module.End ℚ V)))
  haveI : IsScalarTower ℚ A V := ⟨fun q a v => by
    show ρ (q • a) v = q • ρ a v
    rw [Algebra.smul_def, map_mul, Module.End.mul_apply, hρq, Module.algebraMap_end_apply]⟩
  have hV : LinearMap.trace ℚ V (DistribMulAction.toLinearMap ℚ V c) = LinearMap.trace ℚ V (ρ c) := rfl
  have hA : LinearMap.trace ℚ A (DistribMulAction.toLinearMap ℚ A c) =
      Algebra.trace ℚ F (LinearMap.trace F A (LinearMap.mulLeft F c)) := by
    rw [← trace_restrictScalars_rat]
    rfl
  have hsum : (algebraMap ℚ ℂ (Algebra.trace ℚ F (LinearMap.trace F A (LinearMap.mulLeft F c)))) =
      n * ∑ σ, Matrix.trace (ψ σ c) := by
    rw [trace_eq_sum_embeddings ℂ, Finset.mul_sum]
    refine (Fintype.sum_equiv (RingHom.equivRatAlgHom F ℂ).symm _ _ fun τ => ?_)
    exact embedding_trace_mulLeft_eq_mul_trace n hn _ (ψ _) (hψ _) c
  have hdim : Module.finrank ℚ A = Module.finrank ℚ F * n ^ 2 := by
    rw [← hn, Module.finrank_mul_finrank]
  have key := trace_mul_finrank_eq_finrank_mul_trace (A := A) (M := V) c
  rw [hV, hA, hdim] at key
  have key' := congrArg (fun t : ℚ => (t : ℂ)) key
  simp only [Rat.cast_mul, Rat.cast_natCast] at key'
  have hsum' : ((Algebra.trace ℚ F (LinearMap.trace F A (LinearMap.mulLeft F c)) : ℚ) : ℂ) =
      n * ∑ σ, Matrix.trace (ψ σ c) := hsum
  rw [hsum'] at key'
  have hnC : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
  apply mul_left_cancel₀ hnC
  push_cast at key' ⊢
  linear_combination key'

end GlobalTheory.QTrace
end
end

