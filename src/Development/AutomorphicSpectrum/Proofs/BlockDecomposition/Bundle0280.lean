import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Bundle0006
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepUnique
import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0262
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsQuasicoherentOfForallExistsAffine
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0264
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSingleV

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StrictMonoSnocPermEqSuccAbove
section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)

namespace GlobalTheory.CompanionTheory.ConeLocal.SnocPerm

theorem eq_succAbove_of_snoc_eq_perm {n : ℕ} (I : Fin n → Fin (n + 1)) (k : Fin (n + 1))
    (π : Equiv.Perm (Fin (n + 1))) (hI : StrictMono I)
    (h : Fin.snoc (α := fun _ => Fin (n + 1)) I k = ⇑π) : I = k.succAbove := by
  have hcast : ∀ i : Fin n, π i.castSucc = I i := fun i => by
    rw [← h]; simp
  have hlast : π (Fin.last n) = k := by
    rw [← h]; simp
  have hrange : Set.range I = Set.range k.succAbove := by
    rw [Fin.range_succAbove]
    ext y
    simp only [Set.mem_range, Set.mem_compl_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩ hy
      rw [← hcast i, ← hlast] at hy
      exact (Fin.castSucc_lt_last i).ne (π.injective hy)
    · intro hy
      obtain ⟨x, rfl⟩ := π.surjective y
      have hx : x ≠ Fin.last n := fun hx => hy (by rw [hx, hlast])
      obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.2 hx
      exact ⟨i, (hcast i).symm⟩
  exact (StrictMono.range_inj hI (Fin.strictMono_succAbove k)).1 hrange

end GlobalTheory.CompanionTheory.ConeLocal.SnocPerm
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StrongApproxClosureMul
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion

namespace GlobalTheory.CompanionTheory.PlaneSA

theorem SAQ_mul_mem {F : Type} [Field F] [NumberField F] {d β : F} {s : Pl F}
    {x y : Q d β (AF F)} (hx : x ∈ SAQ d β s) (hy : y ∈ SAQ d β s) : x * y ∈ SAQ d β s := by
  obtain ⟨γ, hγ, h, hh, rfl⟩ := hx
  obtain ⟨γ', hγ', h', hh', rfl⟩ := hy
  have hq : qn (rat γ' : Q d β (AF F)) = 1 := by
    have := qn_qmap (Algebra.ofId F (AF F)) γ'
    rw [hγ', map_one] at this
    exact this
  have hs : star (rat γ' : Q d β (AF F)) * rat γ' = 1 := by
    rw [star_mul_eq, hq, map_one]
  have hs' : (rat γ' : Q d β (AF F)) * star (rat γ') = 1 := by
    rw [mul_star_eq, hq, map_one]
  refine ⟨γ * γ', ?_, star (rat γ') * h * rat γ' * h', ⟨?_, ?_⟩, ?_⟩
  · rw [show qn (γ * γ') = qn γ * qn γ' from qn_mul γ γ', hγ, hγ', one_mul]
  · rw [qn_mul, qn_mul, qn_mul, qn_star, hq, hh.1, hh'.1]
    simp
  · intro u hu
    have e1 := hh.2 u hu
    have e2 := hh'.2 u hu
    rw [map_mul, map_mul, map_mul, e1, e2, mul_one, mul_one, ← map_mul, hs, map_one]
  · rw [map_mul]
    have : (rat γ : Q d β (AF F)) * rat γ' * (star (rat γ') * h * rat γ' * h') =
        rat γ * (rat γ' * star (rat γ')) * h * rat γ' * h' := by
      simp only [mul_assoc]
    rw [this, hs', mul_one]
    simp only [mul_assoc]

theorem closure_SAQ_mul : ∀ {F : Type} [Field F] [NumberField F] (d β : F) (s : Pl F),
    ∀ x ∈ closure (SAQ d β s), ∀ y ∈ closure (SAQ d β s), x * y ∈ closure (SAQ d β s) := by
  intro F _ _ d β s x hx y hy
  exact map_mem_closure₂ continuous_mul hx hy fun a ha b hb => SAQ_mul_mem ha hb

end GlobalTheory.CompanionTheory.PlaneSA
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubobjectLeOfAffineCover
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct

namespace GlobalTheory.CompanionTheory.GE

theorem hom_eq_zero_of_basicOpen_cover {X : Scheme.{0}} {M N : X.Modules} (φ : M ⟶ N)
    {ι : Type} (V : ι → X.Opens) (hV : ∀ i, IsAffineOpen (V i)) (hcov : iSup V = ⊤)
    (h : ∀ i (f : Γ(X, V i)) (s : Γ(M, X.basicOpen f)), φ.app (X.basicOpen f) s = 0) :
    φ = 0 := by
  refine Scheme.Modules.hom_ext _ _ fun W ↦ ?_
  ext s
  have hcov' : W ≤ ⨆ p : {p : Σ i, Γ(X, V i) // X.basicOpen p.2 ≤ W}, X.basicOpen p.1.2 := by
    intro x hx
    have hx' : x ∈ iSup V := by rw [hcov]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx'
    obtain ⟨f, hfW, hxf⟩ := (hV i).exists_basicOpen_le ⟨x, hx⟩ hi
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨i, f⟩, hfW⟩, hxf⟩
  refine TopCat.Sheaf.eq_of_locally_eq' (⟨N.presheaf, N.isSheaf⟩ : TopCat.Sheaf Ab X)
    (fun p : {p : Σ i, Γ(X, V i) // X.basicOpen p.2 ≤ W} ↦ X.basicOpen p.1.2) W
    (fun p ↦ homOfLE p.2) hcov' _ _ fun p ↦ ?_
  have nat := ConcreteCategory.congr_hom (φ.mapPresheaf.naturality (homOfLE p.2).op) s
  have e1 : (ConcreteCategory.hom (N.presheaf.map (homOfLE p.2).op)) (φ.app W s) = 0 :=
    nat.symm.trans (h p.1.1 p.1.2 _)
  refine e1.trans ?_
  rw [Scheme.Modules.Hom.zero_app]
  simp

theorem app_basicOpen_eq_zero {X : Scheme.{0}} {M N : X.Modules} [M.IsQuasicoherent] (φ : M ⟶ N)
    {U : X.Opens} (hU : IsAffineOpen U) (h0 : ∀ t : Γ(M, U), φ.app U t = 0) (f : Γ(X, U))
    (s : Γ(M, X.basicOpen f)) : φ.app (X.basicOpen f) s = 0 := by
  obtain ⟨n, t, ht⟩ := ((GlobalTheory.QCoh.isLocalizedModule_resBasicOpen_iff M f).1
    (GlobalTheory.QCoh.isLocalizedModule_resBasicOpen M hU f)).1 s
  have hu : IsUnit (X.presheaf.map (homOfLE (X.basicOpen_le f)).op f ^ n) :=
    (GlobalTheory.QCoh.isUnit_res_of_le_basicOpen f (X.basicOpen_le f) le_rfl).pow n
  have nat := ConcreteCategory.congr_hom
    (φ.mapPresheaf.naturality (homOfLE (X.basicOpen_le f)).op) t
  have key : X.presheaf.map (homOfLE (X.basicOpen_le f)).op f ^ n • φ.app (X.basicOpen f) s = 0 := by
    rw [← Scheme.Modules.Hom.app_smul, ht]
    refine nat.trans ?_
    change (ConcreteCategory.hom (N.presheaf.map (homOfLE (X.basicOpen_le f)).op)) (φ.app U t) = 0
    rw [h0 t]
    simp
  exact (hu.smul_eq_zero).1 key

theorem le_of_secs_subset_cover {X : Scheme.{0}} {E : X.Modules} [E.IsQuasicoherent]
    (S T : Subobject E) (hS : (S : X.Modules).IsQuasicoherent)
    (_hT : (T : X.Modules).IsQuasicoherent) {ι : Type} (V : ι → X.Opens)
    (hV : ∀ i, IsAffineOpen (V i)) (hcov : iSup V = ⊤)
    (h : ∀ i, secs S (V i) ⊆ secs T (V i)) : S ≤ T := by
  have h0 : S.arrow ≫ cokernel.π T.arrow = 0 := by
    refine hom_eq_zero_of_basicOpen_cover _ V hV hcov fun i f s ↦ ?_
    refine app_basicOpen_eq_zero _ (hV i) (fun t ↦ ?_) f s
    obtain ⟨y, hy⟩ := h i ⟨t, rfl⟩
    have hz : (T.arrow ≫ cokernel.π T.arrow).app (V i) y = 0 := by
      rw [cokernel.condition]; rfl
    change (cokernel.π T.arrow).app (V i) (S.arrow.app (V i) t) = 0
    rw [← hy]
    exact hz
  exact Subobject.le_of_comm (Abelian.monoLift T.arrow S.arrow h0) (Abelian.monoLift_comp _ _ _)

end GlobalTheory.CompanionTheory.GE
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SupportProductOverPlaces
section
noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published GlobalTheory.CompanionTheory.PlaneSA Topology
open scoped TensorProduct Quaternion

namespace GlobalTheory.CompanionTheory.PlaneSA.ProdSupp

variable {F : Type} [Field F] [NumberField F] {d β : F}

def place (u : Pl F) (x : Q d β (Kp u)) : Q d β (AF F) :=
  ⟨inc u x.re, inc u x.imI, inc u x.imJ, inc u x.imK⟩

theorem q_ext_places {x y : Q d β (AF F)} (h : ∀ u : Pl F, qmap (proj u) x = qmap (proj u) y) :
    x = y := by
  refine QuaternionAlgebra.ext (adele_ext fun u => ?_) (adele_ext fun u => ?_)
    (adele_ext fun u => ?_) (adele_ext fun u => ?_)
  · exact congrArg QuaternionAlgebra.re (h u)
  · exact congrArg QuaternionAlgebra.imI (h u)
  · exact congrArg QuaternionAlgebra.imJ (h u)
  · exact congrArg QuaternionAlgebra.imK (h u)

theorem qmap_star {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R']
    (f : R →ₐ[F] R') (x : Q d β R) : qmap f (star x) = star (qmap f x) := by
  ext <;> simp [qmap]

theorem qmap_place_same (u : Pl F) (x : Q d β (Kp u)) : qmap (proj u) (place u x) = x := by
  refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_ <;> exact proj_inc_same u _

theorem qmap_place_ne {u u' : Pl F} (h : u' ≠ u) (x : Q d β (Kp u)) :
    qmap (proj u') (place u x) = 0 := by
  refine QuaternionAlgebra.ext ?_ ?_ ?_ ?_ <;> exact proj_inc_ne h _

def atPlace (u : Pl F) (y : Q d β (Kp u)) : Q d β (AF F) := 1 + place u (y - 1)

theorem qmap_atPlace_same (u : Pl F) (y : Q d β (Kp u)) : qmap (proj u) (atPlace u y) = y := by
  rw [atPlace, map_add, map_one, qmap_place_same]
  abel

theorem qmap_atPlace_ne {u u' : Pl F} (h : u' ≠ u) (y : Q d β (Kp u)) :
    qmap (proj u') (atPlace u y) = 1 := by
  rw [atPlace, map_add, map_one, qmap_place_ne h, add_zero]

theorem atPlace_mem_suppAt (u : Pl F) {y : Q d β (Kp u)} (hy : qn y = 1) :
    atPlace u y ∈ SuppAt d β {u} := by
  refine ⟨adele_ext fun u' => ?_, fun u' hu' => qmap_atPlace_ne hu' y⟩
  rw [← qn_qmap, map_one]
  by_cases h : u' = u
  · subst h
    rw [qmap_atPlace_same, hy]
  · rw [qmap_atPlace_ne h, qn_one]

theorem suppAt_empty_eq_one {g : Q d β (AF F)} (hg : g ∈ SuppAt d β (∅ : Set (Pl F))) : g = 1 :=
  q_ext_places fun u => by rw [hg.2 u (Set.notMem_empty u), map_one]

theorem exists_mul_of_mem_insert {u : Pl F} {T : Set (Pl F)} {g : Q d β (AF F)}
    (hg : g ∈ SuppAt d β (insert u T)) :
    ∃ g' ∈ SuppAt d β T, ∃ h ∈ SuppAt d β {u}, g = g' * h := by
  have hy : qn (qmap (proj u) g) = 1 := by rw [qn_qmap, hg.1, map_one]
  have hh := atPlace_mem_suppAt u hy
  set h := atPlace u (qmap (proj u) g) with hdef
  refine ⟨g * star h, ⟨?_, fun u' hu' => ?_⟩, h, hh, ?_⟩
  · rw [qn_mul, qn_star, hg.1, hh.1, one_mul]
  · rw [map_mul, qmap_star]
    by_cases e : u' = u
    · subst e
      rw [hdef, qmap_atPlace_same, mul_star_eq, hy, map_one]
    · rw [hdef, qmap_atPlace_ne e, hg.2 u' (by simp [e, hu']), star_one, one_mul]
  · rw [mul_assoc, star_mul_eq, hh.1, map_one, mul_one]

theorem suppAt_subset_of_places :
    ∀ {F : Type} [Field F] [NumberField F] (d β : F) (N : Set (Q d β (AF F))), (1 : Q d β (AF F)) ∈ N →
      (∀ x ∈ N, ∀ y ∈ N, x * y ∈ N) → (∀ u : Pl F, SuppAt d β {u} ⊆ N) →
      ∀ T : Finset (Pl F), SuppAt d β (T : Set (Pl F)) ⊆ N := by
  intro F _ _ d β N h1 hmul hu T
  classical
  induction T using Finset.induction_on with
  | empty =>
    intro g hg
    rw [Finset.coe_empty] at hg
    rw [suppAt_empty_eq_one hg]
    exact h1
  | insert u T _ ih =>
    intro g hg
    rw [Finset.coe_insert] at hg
    obtain ⟨g', hg', h, hh, rfl⟩ := exists_mul_of_mem_insert hg
    exact hmul _ (ih hg') _ (hu u hh)

end GlobalTheory.CompanionTheory.PlaneSA.ProdSupp
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TaylorOfLocalFrame
section
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)

noncomputable section
namespace GlobalTheory.CompanionTheory.ConeLocal

theorem taylor_alg {K A B : Type} [CommRing K] [CommRing A] [Algebra K A] [CommRing B] [Algebra K B] {d : ℕ}
    (t : Fin d → A)
    (hf : (MvPolynomial.eval₂Hom (algebraMap K A) t : MvPolynomial (Fin d) K →+* A).FormallyUnramified)
    (D : Fin d → Derivation K A A) (hD : ∀ k j, D k (t j) = if k = j then 1 else 0)
    (N P : Ideal B) (hNP : N * N ≤ P) (a b : A →ₐ[K] B) (hab : ∀ x, a x - b x ∈ N) (x : A) :
    a x - b x - ∑ k, (a (t k) - b (t k)) * b (D k x) ∈ P := by
  classical
  let f : MvPolynomial (Fin d) K →+* A := MvPolynomial.eval₂Hom (algebraMap K A) t
  let π : B →+* B ⧸ P := Ideal.Quotient.mk P
  let e : Fin d → B := fun k => a (t k) - b (t k)
  have he : ∀ k, e k ∈ N := fun k => hab _
  let S : A → B := fun x => ∑ k, e k * b (D k x)
  have hS : ∀ x, S x ∈ N := fun x => Ideal.sum_mem _ fun k _ => N.mul_mem_right _ (he k)
  have hSadd : ∀ x y, S (x + y) = S x + S y := fun x y => by
    simp only [S, map_add, mul_add, Finset.sum_add_distrib]
  have hSmul : ∀ x y, S (x * y) = b x * S y + b y * S x := fun x y => by
    simp only [S, Derivation.leibniz, smul_eq_mul, map_add, map_mul, mul_add, Finset.sum_add_distrib,
      Finset.mul_sum]
    congr 1 <;> exact Finset.sum_congr rfl fun k _ => by ring
  have hSone : S 1 = 0 := by simp [S]
  have hSzero : S 0 = 0 := by simp [S]
  let c : A →+* B ⧸ P :=
    { toFun := fun x => π (b x + S x)
      map_one' := by simp [hSone]
      map_zero' := by simp [hSzero]
      map_add' := fun x y => by
        rw [hSadd, map_add b, ← map_add π]
        congr 1
        ring
      map_mul' := fun x y => by
        rw [← map_mul π]
        refine Ideal.Quotient.eq.2 ?_
        have h := hNP (Ideal.mul_mem_mul (hS x) (hS y))
        have e2 : b (x * y) + S (x * y) - (b x + S x) * (b y + S y) = -(S x * S y) := by
          rw [hSmul, map_mul]
          ring
        rw [e2]
        exact P.neg_mem h }
  have hc : ∀ x, c x = π (b x + S x) := fun _ => rfl
  have hcf : c.comp f = π.comp ((a : A →+* B).comp f) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) fun i => ?_
    · simp only [RingHom.comp_apply, f, MvPolynomial.eval₂Hom_C, hc]
      have : S (algebraMap K A r) = 0 := by simp [S]
      simp [this]
    · simp only [RingHom.comp_apply, f, MvPolynomial.eval₂Hom_X', hc]
      have : S (t i) = e i := by simp [S, hD, e]
      rw [this]
      simp [e]
  letI algA : Algebra (MvPolynomial (Fin d) K) A := f.toAlgebra
  letI algC : Algebra (MvPolynomial (Fin d) K) (B ⧸ P) := (π.comp ((a : A →+* B).comp f)).toAlgebra
  haveI : Algebra.FormallyUnramified (MvPolynomial (Fin d) K) A := hf
  let g₁ : A →ₐ[MvPolynomial (Fin d) K] B ⧸ P :=
    { toRingHom := π.comp (a : A →+* B), commutes' := fun _ => rfl }
  let g₂ : A →ₐ[MvPolynomial (Fin d) K] B ⧸ P :=
    { toRingHom := c, commutes' := fun p => RingHom.congr_fun hcf p }
  have hnil : IsNilpotent (N.map π) := by
    refine ⟨2, ?_⟩
    rw [pow_two, ← Ideal.map_mul, Ideal.zero_eq_bot]
    refine le_bot_iff.1 ((Ideal.map_mono hNP).trans ?_)
    rw [Ideal.map_quotient_self]
  have hg : g₁ = g₂ := by
    refine Algebra.FormallyUnramified.ext (N.map π) hnil fun y => ?_
    refine Ideal.Quotient.eq.2 ?_
    have : g₁ y - g₂ y = π (a y - (b y + S y)) := by
      rw [map_sub]
      rfl
    rw [this]
    refine Ideal.mem_map_of_mem π ?_
    have e3 : a y - (b y + S y) = (a y - b y) - S y := by ring
    rw [e3]
    exact N.sub_mem (hab y) (hS y)
  have h1 : π (a x) = π (b x + S x) := DFunLike.congr_fun hg x
  have h2 := Ideal.Quotient.eq.1 h1
  have e4 : a x - (b x + S x) = a x - b x - ∑ k, (a (t k) - b (t k)) * b (D k x) := by
    simp only [S, e]
    ring
  rwa [e4] at h2

theorem taylor_loc : ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {W : X.Opens} {d : ℕ} (c : Coord q W d) (s : ℕ) (E : Frame (sP (KS q s {W})) d)
    (ε : Γ(X, W) ≃+* (sP (KS q s {W})).A.obj E.D), IsLoc q s c.t E ε →
    letI := (strV q W).toAlgebra
    ∀ (D : Fin d → Derivation K Γ(X, W) Γ(X, W)), (∀ k j, D k (c.t j) = if k = j then 1 else 0) →
    Taylor (sFil (KS q s {W})) E (fun k x => ε (D k (ε.symm x))) := by
  intro K _ _ X q W d c s E ε h
  letI := (strV q W).toAlgebra
  intro D hD
  obtain ⟨-, -, h3, h4, h5⟩ := h
  intro T u v x
  obtain ⟨y, rfl⟩ := ε.surjective x
  have hF := GlobalTheory.CompanionTheory.DPFil.isFil_sFil (KS q s {W})
  have hcomm : ∀ (w : E.D ⟶ T) (r : K), ((sP (KS q s {W})).A.map w).hom (ε (algebraMap K Γ(X, W) r)) =
      algebraMap K ((sP (KS q s {W})).A.obj T) r := fun w r => by
    have e : ε (algebraMap K Γ(X, W) r) = algebraMap K _ r := h3 r
    rw [e]
    exact AlgHom.commutes _ r
  let ev' : (E.D ⟶ T) → (Γ(X, W) →ₐ[K] (sP (KS q s {W})).A.obj T) := fun w =>
    { toRingHom := RingHom.comp (AlgHom.toRingHom ((sP (KS q s {W})).A.map w).hom) ε.toRingHom
      commutes' := hcomm w }
  have hNP : (sFil (KS q s {W}) 1).S T * (sFil (KS q s {W}) 1).S T ≤ (sFil (KS q s {W}) 2).S T :=
    Ideal.mul_le.2 fun a ha b hb => hF.mul 1 1 T ha hb
  have hab : ∀ g, ev' u g - ev' v g ∈ (sFil (KS q s {W}) 1).S T := fun g => by
    rw [hF.one T]
    have e := (h4 T u g).symm.trans (h4 T v g)
    exact Ideal.Quotient.eq.1 e
  have hf : (MvPolynomial.eval₂Hom (algebraMap K Γ(X, W)) c.t : MvPolynomial (Fin d) K →+* Γ(X, W)).FormallyUnramified :=
    by
      have he := c.etale
      letI := (MvPolynomial.eval₂Hom (strV q W) c.t : MvPolynomial (Fin d) K →+* Γ(X, W)).toAlgebra
      haveI : Algebra.Etale (MvPolynomial (Fin d) K) Γ(X, W) := he
      exact (inferInstance : Algebra.FormallyUnramified (MvPolynomial (Fin d) K) Γ(X, W))
  have key := taylor_alg c.t hf D hD _ _ hNP (ev' u) (ev' v) hab y
  have e : ∀ k, E.τ k v u = ev' u (c.t k) - ev' v (c.t k) := fun k => h5 k v u
  simp only [ε.symm_apply_apply, e]
  exact key

end GlobalTheory.CompanionTheory.ConeLocal
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TchNeMulOfPowEq
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTPer

theorem exists_monic_eval₂_of_span {A B : Type*} [CommRing A] [CommRing B] (f : A →+* B) (S : Subring B)
    (T : Finset B) (hW : ∀ a, f a ∈ S) (hT : ∀ t ∈ T, t ∈ S)
    (hS : ∀ s ∈ S, ∃ a : B → A, s = ∑ t ∈ T, t * f (a t)) (e : B) (he : e ∈ S) :
    ∃ P : Polynomial A, P.Monic ∧ P.eval₂ f e = 0 := by
  letI : Algebra A B := f.toAlgebra
  let C : Subalgebra A B := { S with algebraMap_mem' := hW }
  have hfg : (Subalgebra.toSubmodule C).FG := by
    refine ⟨T, le_antisymm ?_ ?_⟩
    · exact Submodule.span_le.2 fun t ht => hT t ht
    · intro s hs
      obtain ⟨a, rfl⟩ := hS s hs
      refine Submodule.sum_mem _ fun t ht => ?_
      have : t * f (a t) = a t • t := by
        rw [Algebra.smul_def, mul_comm]; rfl
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ht)
  exact IsIntegral.of_mem_of_fg C hfg e he

theorem pow_natDegree_eq_zero_of_eval₂ {A B R : Type*} [CommRing A] [CommRing B] [CommRing R]
    (f : A →+* B) (hf : Function.Injective f) (c : A →+* R) (P : Polynomial A) (hP : P.Monic)
    (e : B) (he : P.eval₂ f e = 0) (n v : A) (hn : c n = 0) (hv : f n * e = f v) :
    c v ^ P.natDegree = 0 := by
  have h1 : (P.scaleRoots n).eval₂ f (f v) = 0 := by
    rw [← hv, Polynomial.scaleRoots_eval₂_mul, he, mul_zero]
  have h2 : (P.scaleRoots n).eval v = 0 := by
    apply hf
    rw [← Polynomial.eval₂_at_apply, h1, map_zero]
  have h3 : (P.scaleRoots n).eval₂ c (c v) = 0 := by
    rw [Polynomial.eval₂_at_apply, h2, map_zero]
  rw [Polynomial.eval₂_eq_sum_range, Polynomial.natDegree_scaleRoots,
    Finset.sum_eq_single P.natDegree] at h3
  · rw [Polynomial.coeff_scaleRoots, Nat.sub_self, pow_zero, mul_one, Polynomial.coeff_natDegree,
      hP.leadingCoeff, map_one, one_mul] at h3
    exact h3
  · intro i hi hne
    have hlt : i < P.natDegree := lt_of_le_of_ne (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)) hne
    rw [Polynomial.coeff_scaleRoots, map_mul, map_pow, hn, zero_pow (Nat.sub_ne_zero_of_lt hlt)]
    simp
  · intro h
    exact absurd (Finset.mem_range.2 (Nat.lt_succ_self _)) h

theorem tch_ne_mul_of_pow_eq {l : ℕ} [Fact l.Prime] (S : Subring (Formalism.Per6.BdRp l)) (T : Finset (Formalism.Per6.BdRp l)) :
    (∀ a, wB l a ∈ S) → (∀ t ∈ T, t ∈ S) →
    (∀ s ∈ S, ∃ a : Formalism.Per6.BdRp l → Wl l, s = ∑ t ∈ T, t * wB l (a t)) →
    ∀ (ϖ y : Formalism.Per6.BdRp l) (N : ℕ), y ∈ S → ϖ ^ N = (l : Formalism.Per6.BdRp l) * y →
    ∀ u : Tl l, u ≠ 0 → ∀ s ∈ S, tch l u ≠ ϖ * s := by
  intro hW hT hS ϖ y N hy hN u hu s hs h
  haveI := GroundTheory.PAdicHodge.IsPerfectoidField.isDomain_preTilt (K := ℂ_[l]) l
  obtain ⟨P, hP, hev⟩ := exists_monic_eval₂_of_span (wB l) S T hW hT hS (y * s ^ N)
    (S.mul_mem hy (S.pow_mem hs N))
  have hinj : Function.Injective (wB l) := PositivityTheory.LocInh.wittTo_injective
  have hv : wB l (l : Wl l) * (y * s ^ N) = wB l (WittVector.teichmuller l (u ^ N)) := by
    have h1 : wB l (WittVector.teichmuller l (u ^ N)) = tch l u ^ N := by
      rw [map_pow, map_pow]; rfl
    rw [h1, h, mul_pow, hN, map_natCast, mul_assoc]
  have hc : (WittVector.constantCoeff : Wl l →+* Tl l) (l : Wl l) = 0 := by
    rw [map_natCast]
    exact CharP.cast_eq_zero _ _
  have h0 := pow_natDegree_eq_zero_of_eval₂ (wB l) hinj WittVector.constantCoeff P hP _ hev
    (l : Wl l) _ hc hv
  have h2 : (WittVector.constantCoeff : Wl l →+* Tl l) (WittVector.teichmuller l (u ^ N)) = u ^ N :=
    WittVector.teichmuller_coeff_zero l _
  rw [h2] at h0
  exact hu (eq_zero_of_pow_eq_zero (eq_zero_of_pow_eq_zero h0))

end GlobalTheory.CompanionTheory.LTPer
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorInvolutionInvolutive
section
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology

namespace GlobalTheory.CompanionTheory.SaGen

theorem sigR_sigR_eq : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (K : Type) [Field K] [Algebra F K] (t : K ⊗[F] E), sigR K σ (sigR K σ t) = t := by
  intro F E _ _ _ _ _ σ h K _ _ t
  have hσ : ∀ x : E, σ (σ x) = x := by
    intro x
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [h.2.2.2, h.2.2.2, star_star]
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [sigR, hσ]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

end GlobalTheory.CompanionTheory.SaGen
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorNoetherianAffineOpen
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE TensorProduct

namespace GlobalTheory.CompanionTheory.GE

theorem krull_noeth_chart : ∀ {X : Scheme.{0}} (J : X.IdealSheafData) {Z : Scheme.{0}} (ψ : Z ⟶ J.subscheme), IsProper ψ → ∀ (V : X.Opens), IsAffineOpen V → ∀ (U : Z.Opens), IsAffineOpen U → ∀ h : U ≤ (ψ ≫ J.subschemeι) ⁻¹ᵁ V, letI : Algebra Γ(X, V) Γ(Z, U) := ((ψ ≫ J.subschemeι).appLE V U h).hom.toAlgebra; ∀ (R : Type) [CommRing R] [IsNoetherianRing R] [Algebra Γ(X, V) R], IsNoetherianRing (R ⊗[Γ(X, V)] Γ(Z, U)) := by
  intro X J Z ψ hψ V hV U hU h
  have hft : ((ψ ≫ J.subschemeι).appLE V U h).hom.FiniteType := by
    haveI : LocallyOfFiniteType ψ := inferInstance
    haveI : LocallyOfFiniteType (ψ ≫ J.subschemeι) := inferInstance
    exact LocallyOfFiniteType.finiteType_appLE (ψ ≫ J.subschemeι) hV hU h
  letI : Algebra Γ(X, V) Γ(Z, U) := ((ψ ≫ J.subschemeι).appLE V U h).hom.toAlgebra
  intro R _ _ _
  haveI : Algebra.FiniteType Γ(X, V) Γ(Z, U) := by
    exact hft
  haveI : Algebra.FiniteType R (R ⊗[Γ(X, V)] Γ(Z, U)) := inferInstance
  exact Algebra.FiniteType.isNoetherianRing R _

end GlobalTheory.CompanionTheory.GE
end

