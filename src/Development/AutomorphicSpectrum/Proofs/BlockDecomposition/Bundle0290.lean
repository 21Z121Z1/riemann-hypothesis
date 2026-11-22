import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0278
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.BasisB
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0265
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0148
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0142
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0280
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSingleV
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0262
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.PolynomialSiteTraces.AdmissibleMap
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.ExistsDividedPowersAug
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.Bundle0002
import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.RingTrunc
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0253
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0007
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepUnique
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StCocycle
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CupListRepresentativeOfForms
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.ResCoeff
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.InclStd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0281
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryProductReflections
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryQuadraticPairPerturbNearby

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SupportClosureRegularTrace
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion

noncomputable section

namespace GlobalTheory.CompanionTheory.PlaneSA.RegClosure

variable {F : Type} [Field F] [NumberField F] {d β : F}

theorem qmap_re {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (f : R →ₐ[F] R')
    (x : Q d β R) : (qmap f x).re = f x.re := rfl
theorem qmap_imI {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (f : R →ₐ[F] R')
    (x : Q d β R) : (qmap f x).imI = f x.imI := rfl
theorem qmap_imJ {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (f : R →ₐ[F] R')
    (x : Q d β R) : (qmap f x).imJ = f x.imJ := rfl
theorem qmap_imK {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (f : R →ₐ[F] R')
    (x : Q d β R) : (qmap f x).imK = f x.imK := rfl

theorem nhdsNE_neBot_Kp : ∀ u : Pl F, (𝓝[≠] (0 : Kp u)).NeBot
  | .inl w => by
    letI : NontriviallyNormedField w.Completion :=
      { (inferInstance : NormedField w.Completion) with
        non_trivial := ⟨2, by
          have := (InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero
            (map_zero _) 2
          rw [← this, map_ofNat]; norm_num⟩ }
    exact NormedField.nhdsNE_neBot (0 : w.Completion)
  | .inr v => by
    letI := Valued.toNontriviallyNormedField (v.adicCompletion F) (WithZero (Multiplicative ℤ))
    exact NormedField.nhdsNE_neBot (0 : v.adicCompletion F)

theorem two_ne_zero_Kp (u : Pl F) : (2 : Kp u) ≠ 0 := by
  have h : algebraMap F (Kp u) 2 ≠ 0 := (map_ne_zero (algebraMap F (Kp u))).2 two_ne_zero
  rwa [map_ofNat] at h

def psi (w : Pl F) (e : Q d β (Kp w)) : Q d β (AF F) :=
  ⟨1 + inc w (e.re - 1), inc w e.imI, inc w e.imJ, inc w e.imK⟩

theorem qmap_proj_psi_same (w : Pl F) (e : Q d β (Kp w)) : qmap (proj w) (psi w e) = e := by
  ext <;> simp [qmap_re, qmap_imI, qmap_imJ, qmap_imK, psi, proj_inc_same]

theorem qmap_proj_psi_ne {u w : Pl F} (h : u ≠ w) (e : Q d β (Kp w)) :
    qmap (proj u) (psi w e) = 1 := by
  ext <;> simp [qmap_re, qmap_imI, qmap_imJ, qmap_imK, psi, proj_inc_ne h]

theorem eq_of_qmap_proj {x y : Q d β (AF F)} (h : ∀ u, qmap (proj u) x = qmap (proj u) y) : x = y := by
  ext
  · exact adele_ext fun u => by simpa [qmap_re] using congrArg QuaternionAlgebra.re (h u)
  · exact adele_ext fun u => by simpa [qmap_imI] using congrArg QuaternionAlgebra.imI (h u)
  · exact adele_ext fun u => by simpa [qmap_imJ] using congrArg QuaternionAlgebra.imJ (h u)
  · exact adele_ext fun u => by simpa [qmap_imK] using congrArg QuaternionAlgebra.imK (h u)

theorem continuous_psi (w : Pl F) : Continuous (psi (d := d) (β := β) w) := by
  refine continuous_q_iff.2 ⟨?_, ?_, ?_, ?_⟩
  · exact continuous_const.add ((continuous_inc w).comp (continuous_re.sub continuous_const))
  · exact (continuous_inc w).comp continuous_imI
  · exact (continuous_inc w).comp continuous_imJ
  · exact (continuous_inc w).comp continuous_imK

theorem psi_mem {w : Pl F} {e : Q d β (Kp w)} (he : qn e = 1) : psi w e ∈ SuppAt d β {w} := by
  refine ⟨adele_ext fun u => ?_, fun u hu => qmap_proj_psi_ne (by simpa using hu) e⟩
  rw [← qn_qmap, map_one]
  by_cases h : u = w
  · subst h
    rw [qmap_proj_psi_same, he]
  · rw [qmap_proj_psi_ne h, qn_one]

theorem psi_proj {w : Pl F} {a : Q d β (AF F)} (ha : a ∈ SuppAt d β {w}) :
    a = psi w (qmap (proj w) a) := by
  refine eq_of_qmap_proj fun u => ?_
  by_cases h : u = w
  · subst h
    rw [qmap_proj_psi_same]
  · rw [qmap_proj_psi_ne h, ha.2 u (by simpa using h)]

theorem reg_closure : ∀ {F : Type} [Field F] [NumberField F] (d β : F), d ≠ 0 → β ≠ 0 → ∀ w : Pl F, ∀ a ∈ SuppAt d β {w},
  a ∈ closure {a' | a' ∈ SuppAt d β {w} ∧ (qmap (proj w) a').re ^ 2 ≠ 1} := by
  intro F _ _ d β hd hb w a ha
  rw [mem_closure_iff_nhds]
  intro U hU
  have hpa := psi_proj ha
  rw [hpa] at hU
  have hU' : psi w ⁻¹' U ∈ 𝓝 (qmap (proj w) a) := (continuous_psi w).continuousAt hU
  have hn : qn (qmap (proj w) a) = 1 := by rw [qn_qmap, ha.1, map_one]
  obtain ⟨b, hbU, hb1, hb2⟩ := RegDense.regular_dense d β (two_ne_zero_Kp w) hd hb
    (nhdsNE_neBot_Kp w) _ hn _ hU'
  exact ⟨psi w b, hbU, psi_mem hb1, by rw [qmap_proj_psi_same]; exact hb2⟩

end GlobalTheory.CompanionTheory.PlaneSA.RegClosure
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensTransportSymm
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section

namespace GlobalTheory.CompanionTheory.GlobBc

universe w w'

theorem tens_transport {R : Type} [CommRing R] {ι : Type} [DecidableEq ι] {N : ι → Type} [∀ i, AddCommGroup (N i)]
    [∀ i, Module R (N i)] {M M₁ : ι → Type w} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, AddCommGroup (M₁ i)] [∀ i, Module R (M₁ i)] {M' M₁' : Type w'} [AddCommGroup M'] [AddCommGroup M₁']
    {f : ∀ i, N i → M i → M'} {f₁ : ∀ i, N i → M₁ i → M₁'}
    (e : ∀ i, M i ≃ₗ[R] M₁ i) (e' : M' ≃+ M₁') (h : ∀ i n x, e' (f i n x) = f₁ i n (e i x))
    (hT : Tens R f) : Tens R f₁ := by
  obtain ⟨g, hg⟩ := hT
  let c : (∀ i, N i ⊗[R] M₁ i) ≃+ (∀ i, N i ⊗[R] M i) :=
    AddEquiv.piCongrRight fun i => (TensorProduct.congr (LinearEquiv.refl R (N i)) (e i).symm).toAddEquiv
  refine ⟨c.trans (g.trans e'), fun i n x => ?_⟩
  have hc : c (Pi.single i (n ⊗ₜ x)) = Pi.single i (n ⊗ₜ (e i).symm x) := by
    funext k
    by_cases hk : k = i
    · subst hk
      simp [c]
    · simp [c, Pi.single_eq_of_ne hk]
  simp only [AddEquiv.trans_apply]
  rw [hc, hg, h, LinearEquiv.apply_symm_apply]

theorem tens_transport_symm {R : Type} [CommRing R] {ι : Type} [DecidableEq ι] {N : ι → Type} [∀ i, AddCommGroup (N i)]
    [∀ i, Module R (N i)] {M M₁ : ι → Type w} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, AddCommGroup (M₁ i)] [∀ i, Module R (M₁ i)] {M' M₁' : Type w'} [AddCommGroup M'] [AddCommGroup M₁']
    {f : ∀ i, N i → M i → M'} {f₁ : ∀ i, N i → M₁ i → M₁'}
    (e : ∀ i, M i ≃ₗ[R] M₁ i) (e' : M' ≃+ M₁') (h : ∀ i n x, e' (f i n x) = f₁ i n (e i x))
    (hT : Tens R f₁) : Tens R f :=
  tens_transport (fun i => (e i).symm) e'.symm
    (fun i n x => by rw [AddEquiv.symm_apply_eq, h, LinearEquiv.apply_symm_apply]) hT

section
variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {I : Ideal A} (γ : DividedPowers I)
  {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O))

def thM : SMor (thP (nlFun (dividedPowersBot O) 0 X q (Ideal.Quotient.mk ⊥))) (thP (nlFun γ 0 X q (κA O I)))
    (algebraMap O A) where
  G := ((nmO γ q).mor 0).functor
  ρ T := RingHom.id _
  comm _ _ := rfl
  nat _ _ := rfl
  mem _ _ hx := hx
  dp _ _ _ _ := rfl

theorem leC {c : A} {i : ℕ} (hc : c ∈ pdP γ i) (r : ℤ) :
    (thM γ q).LeC c (thFil _ (r - i)) (thFil _ r) := by
  intro T x hx
  have h1 : T.i c ∈ pdP T.δ i := dividedPowerFiltration_map T.compat i hc
  have h2 : x ∈ pdP T.δ (r - i).toNat := hx
  have h3 := GlobalTheory.CompanionTheory.DPFil.dividedPowerFiltration_mul_le T.δ _ _ (Ideal.mul_mem_mul h1 h2)
  exact T.pdPow_anti (by omega) h3

end

abbrev rq {b : Base} {L : b.Fun} {Q Q' : ObjectProperty (Thick L)} (h : Q' ≤ Q) (r r' : ℤ) :
    CH.Mor (sq (sFil Q r) (sFil Q r')) (sq (sFil Q' r) (sFil Q' r')) (RingHom.id _) :=
  (incl h).sq (incl_fil h r) (incl_fil h r')

section
variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {I : Ideal A} (γ : DividedPowers I)
  {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) (l s : ℕ) {m : ℕ} (S : GrSplit O γ m)

theorem leS (𝒱 : Set X.Opens) (i : Fin m) (n : S.N i) (r : ℤ) :
    (smO γ q l s 𝒱).LeC (S.ν i n) (sFil _ (r - i)) (sFil _ r) :=
  fun T x hx => leC γ q (S.mem i n) r T.obj x hx

abbrev mC (𝒱 : Set X.Opens) (r r' : ℤ) (i : Fin m) (n : S.N i) :=
  (smO γ q l s 𝒱).sqC (S.ν i n) (leS γ q l s S 𝒱 i n r) (leS γ q l s S 𝒱 i n r')

def BcAt (𝒱 : Set X.Opens) (r r' : ℤ) (j : ℕ) : Prop :=
  Tens O (N := S.N) (M := fun i => HQ (TO q l s 𝒱) (r - i) (r' - i) j) (M' := HQ (TS γ q l s 𝒱) r r' j)
    fun i n x => (mC γ q l s S 𝒱 r r' i n).pull j x

variable {γ q l s}

theorem st_top {R : Type} [CommRing R] {J : Ideal R} {δ : DividedPowers J} {p : ℕ} {κ : O →+* R ⧸ J}
    (Q : ObjectProperty (Thick (nlFun δ p X q κ))) (𝒱 : Set X.Opens) : St Q 𝒱 ≤ St Q {⊤} := by
  rintro T ⟨h, V, -, -⟩
  exact ⟨h, ⊤, rfl, fun _ _ => trivial⟩

theorem comm_top (𝒱 : Set X.Opens) (r r' : ℤ) (j : ℕ) (i : Fin m) (n : S.N i) (x) :
    (rq (st_top (TF l s) 𝒱) r r').pull j ((mC γ q l s S {⊤} r r' i n).pull j x) =
    (mC γ q l s S 𝒱 r r' i n).pull j ((rq (st_top (TF l s) 𝒱) (r - i) (r' - i)).pull j x) := by
  refine ((CrystallineSemistableComparison.P.pull_comp (σ'' := algebraMap O A) (mC γ q l s S {⊤} r r' i n) (rq (st_top (TF l s) 𝒱) r r') j x).1).symm.trans
    (Eq.trans ?_ ((CrystallineSemistableComparison.P.pull_comp (σ'' := algebraMap O A) (rq (st_top (TF l s) 𝒱) (r - i) (r' - i)) (mC γ q l s S 𝒱 r r' i n) j x).1))
  refine CrystallineSemistableComparison.P.prism (σ := algebraMap O A) ((mC γ q l s S {⊤} r r' i n).comp (rq (st_top (TF l s) 𝒱) r r'))
    ((rq (st_top (TF l s) 𝒱) (r - i) (r' - i)).comp (mC γ q l s S 𝒱 r r' i n)) (𝟙 _) (fun T y => ?_) j x
  obtain ⟨y, hy⟩ := y
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
  first
    | rfl
    | (simp only [NatTrans.id_app, CategoryTheory.Functor.map_id]; rfl)

theorem used_TF {R : Type} [CommRing R] {J : Ideal R} {δ : DividedPowers J} {κ : O →+* R ⧸ J} (l s : ℕ) :
    Used (TF l s : ObjectProperty (Thick (nlFun δ 0 X q κ))) :=
  Or.inl ⟨rfl, l, s, rfl⟩

theorem bcAt_iff (𝒱 : Set X.Opens) (h𝒱 : sSup 𝒱 = ⊤) (r r' : ℤ) (j : ℕ) :
    BcAt γ q l s S {⊤} r r' j ↔ BcAt γ q l s S 𝒱 r r' j := by
  have hc : ∀ W ∈ ({⊤} : Set X.Opens), W ≤ sSup 𝒱 := fun W hW => by rw [h𝒱]; exact le_top
  have bO := (GlobalTheory.T.cech_refinement_cohomology_bijective (γ := dividedPowersBot O) (p := 0) (q := q) (κ := Ideal.Quotient.mk (⊥ : Ideal O)) (TF l s) (used_TF l s) 𝒱 {⊤} (st_top _ _) hc j).1
  have bA := (GlobalTheory.T.cech_refinement_cohomology_bijective (γ := γ) (p := 0) (q := q) (κ := κA O I) (TF l s) (used_TF l s) 𝒱 {⊤} (st_top _ _) hc j).1
  let eO : ∀ i : Fin m, HQ (TO q l s {⊤}) (r - i) (r' - i) j ≃ₗ[O] HQ (TO q l s 𝒱) (r - i) (r' - i) j := fun i =>
    LinearEquiv.ofBijective ((rq (st_top (TF l s) 𝒱) (r - i) (r' - i)).pull j) (bO _ _)
  let eA : HQ (TS γ q l s {⊤}) r r' j ≃+ HQ (TS γ q l s 𝒱) r r' j :=
    (LinearEquiv.ofBijective ((rq (st_top (TF l s) 𝒱) r r').pull j) (bA _ _)).toAddEquiv
  have hcomm : ∀ i n x, eA ((mC γ q l s S {⊤} r r' i n).pull j x) = (mC γ q l s S 𝒱 r r' i n).pull j (eO i x) :=
    fun i n x => comm_top S 𝒱 r r' j i n x
  exact ⟨tens_transport eO eA hcomm, tens_transport_symm eO eA hcomm⟩

end

section
variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {I : Ideal A} (γ : DividedPowers I)
  {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) {m : ℕ} (S : GrSplit O γ m)

abbrev thO (q : X ⟶ Spec (CommRingCat.of O)) (r r' : ℤ) :
    Thick (nlFun (dividedPowersBot O) 0 X q (Ideal.Quotient.mk ⊥)) ⥤ ModuleCat.{0} O :=
  sq (thFil _ r) (thFil _ r')

abbrev thS (r r' : ℤ) : Thick (nlFun γ 0 X q (κA O I)) ⥤ ModuleCat.{0} A :=
  sq (thFil _ r) (thFil _ r')

abbrev tM (r r' : ℤ) (i : Fin m) (n : S.N i) : CH.Mor (thO q (r - i) (r' - i)) (thS γ q r r') (algebraMap O A) :=
  (thM γ q).sqC (S.ν i n) (leC γ q (S.mem i n) r) (leC γ q (S.mem i n) r')

theorem tM_add (r r' : ℤ) (i : Fin m) (n n' : S.N i) (T) (x) :
    (tM γ q S r r' i (n + n')).τ T x = (tM γ q S r r' i n).τ T x + (tM γ q S r r' i n').τ T x := by
  obtain ⟨y, hy⟩ := x
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
  refine Subtype.ext ?_
  let B := (thA (nlFun γ 0 X q (κA O I))).obj T
  let z' : B := z
  have e : algebraMap A B (S.ν i (n + n')) * z' = algebraMap A B (S.ν i n) * z' + algebraMap A B (S.ν i n') * z' := by
    rw [map_add, map_add, add_mul]
  exact congrArg (Ideal.Quotient.mk ((thFil (nlFun γ 0 X q (κA O I)) r').S T)) e

theorem tM_smul (r r' : ℤ) (i : Fin m) (c : O) (n : S.N i) (T) (x) :
    (tM γ q S r r' i (c • n)).τ T x = algebraMap O A c • (tM γ q S r r' i n).τ T x := by
  obtain ⟨y, hy⟩ := x
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
  refine Subtype.ext ?_
  let B := (thA (nlFun γ 0 X q (κA O I))).obj T
  let z' : B := z
  have e : algebraMap A B (S.ν i (c • n)) * z' = algebraMap O A c • (algebraMap A B (S.ν i n) * z') := by
    rw [map_smul, Algebra.smul_def c, map_mul, mul_assoc, Algebra.smul_def (algebraMap O A c)]
  exact congrArg (Ideal.Quotient.mk ((thFil (nlFun γ 0 X q (κA O I)) r').S T)) e

end

theorem main : KH.GlobBcSt → BcOn True → BcOn False := by
  intro hG hT O A _ _ _ I γ l s m hO hA S X q 𝒱 hc r r' hrr hr's ha hb j
  obtain ⟨U, h𝒱⟩ : Nonempty (Cov q) ∧ sSup 𝒱 = ⊤ := by
    rcases hc with ⟨h, -⟩ | ⟨-, h⟩
    · exact h.elim
    · exact h
  obtain ⟨U⟩ := U
  have hU : sSup (Set.range U.U) = ⊤ := by rw [sSup_range]; exact U.cover
  have hmem : ∀ (𝒲 : Set X.Opens) (T), St (TF l s) 𝒲 T → St (TF l s) 𝒲 ((((nmO γ q).mor 0).functor).obj T) :=
    fun 𝒲 T h => nmO_mem γ q l s 𝒲 T h
  have key : ∀ j, BcAt γ q l s S (Set.range U.U) r r' j := fun j =>
    hG (O := O) (R := O) (I := ⊥) (γ := dividedPowersBot O) (p := 0) (X := X) (q := q) (κ := Ideal.Quotient.mk ⊥)
      (O' := O) (R' := A) (I' := I) (γ' := γ) (p' := 0) (X' := X) (q' := q) (κ' := κA O I)
      (Λ := O) (Λ' := A) (σ := algebraMap O A) ((nmO γ q).mor 0).functor S.N
      (fun i => thO q (r - i) (r' - i)) (thS γ q r r')
      (fun i n T => (tM γ q S r r' i n).τ T) (fun i n {T T'} φ x => (tM γ q S r r' i n).nat φ x)
      (fun i n n' T x => tM_add γ q S r r' i n n' T x) (fun i c n T x => tM_smul γ q S r r' i c n T x)
      (TF l s) (TF l s) U.U U.U (fun α T h => hmem _ T h) (fun S' T h => hmem _ T h) (fun T h => hmem _ T h)
      (fun S' hS' j => by
        obtain ⟨α, hα⟩ := hS'
        obtain ⟨c', -⟩ := GlobalTheory.T.coordinates_restrict_affine_open (U.c α) (iInf₂_le α hα : (⨅ α ∈ S', U.U α) ≤ U.U α) (U.inter S' ⟨α, hα⟩)
        exact hT γ l s m hO hA S q {⨅ α ∈ S', U.U α} (Or.inl ⟨trivial, _, _, rfl, ⟨c'⟩⟩) r r' hrr hr's
          (fun i n => leS γ q l s S _ i n r) (fun i n => leS γ q l s S _ i n r') j) j
  exact (bcAt_iff S 𝒱 h𝒱 r r' j).1 ((bcAt_iff S (Set.range U.U) hU r r' j).2 (key j))

end GlobalTheory.CompanionTheory.GlobBc
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorInvolutionInvolutiveStatement
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_involution_involutive : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (K : Type) [Field K] [Algebra F K] (t : K ⊗[F] E), sigR K σ (sigR K σ t) = t := by
  first | exact @GlobalTheory.CompanionTheory.SaGen.sigR_sigR_eq | exact GlobalTheory.CompanionTheory.SaGen.sigR_sigR_eq | (intros; apply GlobalTheory.CompanionTheory.SaGen.sigR_sigR_eq <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorNoetherianAffineOpenStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_noetherian_affine_open : ∀ {X : Scheme.{0}} (J : X.IdealSheafData) {Z : Scheme.{0}} (ψ : Z ⟶ J.subscheme), IsProper ψ → ∀ (V : X.Opens), IsAffineOpen V → ∀ (U : Z.Opens), IsAffineOpen U → ∀ h : U ≤ (ψ ≫ J.subschemeι) ⁻¹ᵁ V, letI : Algebra Γ(X, V) Γ(Z, U) := ((ψ ≫ J.subschemeι).appLE V U h).hom.toAlgebra; ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [Algebra Γ(X, V) R], IsNoetherianRing (R ⊗[Γ(X, V)] Γ(Z, U)) := by
  first | exact @GlobalTheory.CompanionTheory.GE.krull_noeth_chart | exact GlobalTheory.CompanionTheory.GE.krull_noeth_chart | (intros; apply GlobalTheory.CompanionTheory.GE.krull_noeth_chart <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickJIsNilpotent
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.PDA CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Site

namespace GlobalTheory.CompanionTheory.SiteNil

theorem thick_J_isNilpotent : ∀ {O R : Type} [CommRing O] [CommRing R] {I : Ideal R}
    {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)}
    {κ : O →+* R ⧸ I} (T : Thick (nlFun γ p X q κ)), ∀ x ∈ T.J, IsNilpotent x := by
  intro O R _ _ I γ p X q κ T x hx
  by_cases hp : p = 0
  · obtain ⟨n, hn⟩ := T.adm.2 hp
    refine ⟨n, ?_⟩
    have h : x ^ n ∈ T.J ^ n := Ideal.pow_mem_pow hx n
    rw [hn] at h
    exact h
  · obtain ⟨n, hn⟩ : IsNilpotent ((p : ℕ) : T.B) := T.adm.1 hp
    refine ⟨p * n, ?_⟩
    have h1 : x ^ p = (p.factorial : T.B) * T.δ.dpow p x := (T.δ.factorial_mul_dpow_eq_pow hx).symm
    have h2 : (p.factorial : T.B) = (p : T.B) * ((p - 1).factorial : T.B) := by
      rw [← Nat.cast_mul, Nat.mul_factorial_pred hp]
    rw [pow_mul, h1, h2, mul_assoc, mul_pow, hn, zero_mul]

end GlobalTheory.CompanionTheory.SiteNil
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TopRepresentativeAdd
section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section
namespace GlobalTheory.CompanionTheory.ConeLocal.XdtAdd

open GlobalTheory.CompanionTheory.CupRep

variable {K : Type} [CommRing K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)}

theorem mk_liftV {V : X.Opens} (T : Thick (smFun X q)) (h : InU V T) (g : Γ(X, V)) :
    Ideal.Quotient.mk T.J (liftV T h g) = ev T h g :=
  Classical.choose_spec (Ideal.Quotient.mk_surjective (ev T h g))

theorem liftV_sub_map_mem {V : X.Opens} {T T' : Thick (smFun X q)} (φ : T ⟶ T') (h : InU V T) (h' : InU V T')
    (g : Γ(X, V)) : liftV T' h' g - φ.φ (liftV T h g) ∈ T'.J := by
  refine Ideal.Quotient.eq.1 ?_
  rw [mk_liftV]
  have e : Ideal.Quotient.mk T'.J (φ.φ (liftV T h g)) =
      Ideal.quotientMap T'.J φ.φ φ.hle (Ideal.Quotient.mk T.J (liftV T h g)) := (Ideal.quotientMap_mk).symm
  rw [e, mk_liftV]
  exact GlobalTheory.CompanionTheory.GrForm.ev_nat φ h h' g

theorem liftV_add_mem {V : X.Opens} (T : Thick (smFun X q)) (h : InU V T) (x y : Γ(X, V)) :
    liftV T h x + liftV T h y - liftV T h (x + y) ∈ T.J := by
  refine Ideal.Quotient.eq_zero_iff_mem.1 ?_
  rw [map_sub, map_add, mk_liftV, mk_liftV, mk_liftV, map_add, sub_self]

variable (s : ℕ) (V : X.Opens)

theorem addC_mem (g : Γ(X, V)) :
    addC (KS q s {V}) (fun T => liftV T.obj (ks_in q s V T.obj T.property) g) ∈
      FC (sFil (KS q s {V}) ((1 : ℕ) : ℤ)) 1 := by
  refine mem_FC.2 fun u => ?_
  have hF := GlobalTheory.CompanionTheory.DPFil.isFil_sFil (KS q s {V})
  rw [Nat.cast_one, hF.one]
  exact liftV_sub_map_mem (u.map (homOfLE (Fin.zero_le (Fin.last 1)))).hom _ _ g

theorem cupList_mem {d : ℕ} (l : Fin d → CH.Cn (CH.modF (sP (KS q s {V})).A) 1)
    (hl : ∀ k, l k ∈ FC (sFil (KS q s {V}) ((1 : ℕ) : ℤ)) 1) :
    cupListC (sP (KS q s {V})).A l ∈ FC (sFil (KS q s {V}) ((d : ℕ) : ℤ)) d := by
  have hF := GlobalTheory.CompanionTheory.DPFil.isFil_sFil (KS q s {V})
  induction d with
  | zero =>
    refine mem_FC.2 fun u => ?_
    rw [hF.top _ (by simp)]
    trivial
  | succ n ih =>
    exact cup_mem hF (by omega) (ih _ fun i => hl _) (hl (Fin.last n))

theorem xdtC_val {d : ℕ} (t : Fin d → Γ(X, V)) (x : Γ(X, V)) (u : ComposableArrows (KS q s {V}).FullSubcategory d) :
    vl (xdtC (q := q) s V t x) u =
      ((sP (KS q s {V})).A.map (u.map (homOfLE (Fin.le_last (CH.front (Nat.zero_add d) (Fin.last 0)))))).hom
        (liftV (u.obj (CH.front (Nat.zero_add d) (Fin.last 0))).obj
          (ks_in q s V _ (u.obj (CH.front (Nat.zero_add d) (Fin.last 0))).property) x) *
      vl (cupListC (sP (KS q s {V})).A fun k =>
        addC _ fun T => liftV T.obj (ks_in q s V T.obj T.property) (t k)) u :=
  congrArg (fun b : (sP (KS q s {V})).A.obj (u.obj (Fin.last d)) =>
      ((sP (KS q s {V})).A.map (u.map (homOfLE (Fin.le_last (CH.front (Nat.zero_add d) (Fin.last 0)))))).hom
        (liftV (u.obj (CH.front (Nat.zero_add d) (Fin.last 0))).obj
          (ks_in q s V _ (u.obj (CH.front (Nat.zero_add d) (Fin.last 0))).property) x) * b)
    (CrystallineSemistableComparison.Auxff.term_id _ u _ _ _ (fun t => by simp [CH.back]))

end GlobalTheory.CompanionTheory.ConeLocal.XdtAdd

namespace GlobalTheory.CompanionTheory.ConeLocal

open GlobalTheory.CompanionTheory.CupRep XdtAdd

theorem rep_xdtC_add {K : Type} [Field K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)} (s : ℕ) (V : X.Opens)
    {d : ℕ} (t : Fin d → Γ(X, V)) (x y : Γ(X, V)) (a b : HQ (KS q s {V}) d ((d : ℤ) + 1) d)
    (ha : Rep (sFil (KS q s {V}) d) (sFil (KS q s {V}) ((d : ℤ) + 1)) (xdtC s V t x) a)
    (hb : Rep (sFil (KS q s {V}) d) (sFil (KS q s {V}) ((d : ℤ) + 1)) (xdtC s V t y) b) :
    Rep (sFil (KS q s {V}) d) (sFil (KS q s {V}) ((d : ℤ) + 1)) (xdtC s V t (x + y)) (a + b) := by
  have hF := GlobalTheory.CompanionTheory.DPFil.isFil_sFil (KS q s {V})
  refine rep_congr (rep_add ha hb) fun u => ?_
  have hc := mem_FC.1 (cupList_mem s V (fun k => addC (KS q s {V}) fun T =>
    liftV T.obj (ks_in q s V T.obj T.property) (t k)) fun k => addC_mem s V (t k)) u
  let T0 := u.obj (CH.front (Nat.zero_add d) (Fin.last 0))
  let ψ := u.map (homOfLE (Fin.le_last (CH.front (Nat.zero_add d) (Fin.last 0))))
  have h1 : ((sP (KS q s {V})).A.map ψ).hom
      (liftV T0.obj (ks_in q s V _ T0.property) x + liftV T0.obj (ks_in q s V _ T0.property) y -
        liftV T0.obj (ks_in q s V _ T0.property) (x + y)) ∈ (sFil (KS q s {V}) ((1 : ℕ) : ℤ)).S _ := by
    rw [Nat.cast_one, hF.one]
    exact (sP (KS q s {V})).J.map_mem ψ (liftV_add_mem T0.obj _ x y)
  have h2 := hF.mul 1 d _ h1 hc
  have e : ((1 + d : ℕ) : ℤ) = (d : ℤ) + 1 := by push_cast; ring
  rw [e] at h2
  change vl (xdtC (q := q) s V t x) u + vl (xdtC (q := q) s V t y) u - vl (xdtC (q := q) s V t (x + y)) u ∈ _
  rw [xdtC_val, xdtC_val, xdtC_val]
  convert h2 using 1
  rw [map_sub, map_add]
  ring

end GlobalTheory.CompanionTheory.ConeLocal
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TruncatedWittIsNoetherian
section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.WittLevel

theorem isNoetherianRing_Wm_one :
    ∀ {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l],
      IsNoetherianRing (Wc.Wm l k 1) := by
  intro l _ k _ _ _
  unfold Wc.Wm
  infer_instance

end GlobalTheory.CompanionTheory.WittLevel
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryLiftDetOneApproxPairStatement
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_lift_det_one_approx_pair : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ {M : ℕ} (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ {K : Type} [NontriviallyNormedField K] [Algebra F K] (P : PlaceMap F K) (L : HA K σ J →* HA (AF F) σ J), IsLift P σ J L → (∀ x : HA K σ J, ((HA.mat K σ J x).1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)).det = 1 → L x ∈ SUSupp σ J (P.inj 1)) → ∀ (a b : Fin M → E) (x : HA K σ J), IsQPairOf (sigR K σ) (JR K J) (incV K a) (incV K b) ((HA.mat K σ J x).1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)) → L x ∈ PlaneSupp σ J (P.inj 1) a b := by
  first | exact @GlobalTheory.CompanionTheory.SaGen.LiftPlane.lift_plane | exact GlobalTheory.CompanionTheory.SaGen.LiftPlane.lift_plane | (intros; apply GlobalTheory.CompanionTheory.SaGen.LiftPlane.lift_plane <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryProductReflectionsStatement
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_product_reflections : ∀ {R : Type} [CommRing R] (c : R →+* R), (∀ x, c (c x) = x) → NormOneGen c → ∀ {M : ℕ} (Jm : Matrix (Fin M) (Fin M) R), (∀ i j, c (Jm j i) = Jm i j) → ∀ e : Fin M → Fin M → R, (∀ i j, i ≠ j → Formalism.UG.hform c Jm (e i) (e j) = 0) → (∀ i, IsUnit (Formalism.UG.hform c Jm (e i) (e i))) → IsUnit (Matrix.of e).det → ∀ x : GL (Fin M) R, x ∈ Formalism.UG.UJ c Jm → ∃ l : List (GL (Fin M) R), (∀ y ∈ l, y ∈ Formalism.UG.UJ c Jm ∧ IsQR c Jm (y : Matrix (Fin M) (Fin M) R)) ∧ l.prod = x := by
  first | exact @GlobalTheory.CompanionTheory.SaGen.ReflList.exists_qr_list | exact GlobalTheory.CompanionTheory.SaGen.ReflList.exists_qr_list | (intros; apply GlobalTheory.CompanionTheory.SaGen.ReflList.exists_qr_list <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitaryQuadraticPairPerturbNearbyStatement
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitary_quadratic_pair_perturb_nearby : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ {M : ℕ} (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ {K : Type} [NontriviallyNormedField K] [Algebra F K] (a₀ b₀ : Fin M → K ⊗[F] E) (x : HA K σ J), IsQPairOf (sigR K σ) (JR K J) a₀ b₀ ((HA.mat K σ J x).1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)) → ∀ V ∈ nhds x, ∀ᶠ p in nhds (a₀, b₀), ∃ x' ∈ V, IsQPairOf (sigR K σ) (JR K J) p.1 p.2 ((HA.mat K σ J x').1 : Matrix (Fin M) (Fin M) (K ⊗[F] E)) := by
  first | exact @GlobalTheory.CompanionTheory.SaGen.NearPair.near_pair_main | exact GlobalTheory.CompanionTheory.SaGen.NearPair.near_pair_main | (intros; apply GlobalTheory.CompanionTheory.SaGen.NearPair.near_pair_main <;> assumption)
end

