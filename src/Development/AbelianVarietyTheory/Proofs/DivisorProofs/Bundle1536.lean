import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1517
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1451
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1479
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1484
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1470
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0340
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0322
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1518
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1368
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1252
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1462
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeSkewSignature
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0331
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1387
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0282
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1504
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormBlockEmbLeftInvariant
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1519
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1521
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.UnitaryHaarVolume

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeOneFormFrameAndSquareStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_oneFormFrame_and_square : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → HasFrame (OAff A.hom) ∧ CohomZeroIsConstants (OAff A.hom) ∧ IsAbelianScheme (A ⊗ A) ∧ SmoothOfRelativeDimension (g + g) (A ⊗ A).hom := by
  first | exact @GlobalTheory.AbCoh.basic_of_isAbelianScheme | exact GlobalTheory.AbCoh.basic_of_isAbelianScheme | (intros; apply GlobalTheory.AbCoh.basic_of_isAbelianScheme <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzFixedBySmallHeisenbergLatticeStatement
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicSchwartz_fixed_by_small_heisenberg_lattice : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (ψ : AddChar (AF F) ℂ), Continuous ψ →
    ∀ Φ ∈ schA F κ, ∃ N : ℕ, 1 ≤ N ∧ ∀ w : (κ → AF F) × (κ → AF F),
      (∀ i, (w.1 i).1 = 0 ∧ GlobalTheory.FinSupp.FinDiv F N (w.1 i) ∧ (w.2 i).1 = 0 ∧ GlobalTheory.FinSupp.FinDiv F N (w.2 i)) →
      schr ψ w Φ = Φ := by
  first | exact @GlobalTheory.FinSuppHeis.heis_fix_finDiv | exact GlobalTheory.FinSuppHeis.heis_fix_finDiv | (intros; apply GlobalTheory.FinSuppHeis.heis_fix_finDiv <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentRefl
section
set_option autoImplicit false

open CategoryTheory

namespace GlobalTheory.Vert.Flag

variable {X : AlgebraicGeometry.Scheme.{0}} {E : X.Modules} {N : ℕ}

def SameStep (fl fl' : Flag E N) (i : Fin (N + 1)) : Prop :=
  ∃ e : fl.F i ≅ fl'.F i, e.hom ≫ fl'.ι i = fl.ι i

def Adjacent (fl fl' : Flag E N) : Prop :=
  ∃ j : Fin (N + 1), ∀ i, i ≠ j → fl.SameStep fl' i

theorem sameStep_refl (fl : Flag E N) (i : Fin (N + 1)) : fl.SameStep fl i :=
  ⟨Iso.refl _, Category.id_comp _⟩

theorem SameStep.symm {fl fl' : Flag E N} {i : Fin (N + 1)} (h : fl.SameStep fl' i) :
    fl'.SameStep fl i := by
  obtain ⟨e, he⟩ := h
  exact ⟨e.symm, by rw [Iso.symm_hom, ← he, Iso.inv_hom_id_assoc]⟩

theorem adjacent_refl (fl : Flag E N) : fl.Adjacent fl := ⟨0, fun i _ => fl.sameStep_refl i⟩

theorem Adjacent.symm {fl fl' : Flag E N} (h : fl.Adjacent fl') : fl'.Adjacent fl := by
  obtain ⟨j, hj⟩ := h
  exact ⟨j, fun i hi => (hj i hi).symm⟩

end GlobalTheory.Vert.Flag
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanTraceSymplecticOrthonormalFramesStatement
section
open scoped TensorProduct Matrix Classical GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift
open GlobalTheory.HoweD
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.archimedean_trace_symplectic_orthonormal_frames : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {α β : Type}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {P Q R S : InfinitePlace F → ℕ} (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E)) (a b : ℂ) (A : ∀ w : InfinitePlace F, Matrix α (Ix (P w) (Q w)) ℂ)
    (C : ∀ w : InfinitePlace F, Matrix β (Ix (R w) (S w)) ℂ), IsCMExt F E σ → FramedD τ JA JB a b A C →
    ∀ (u u' : Matrix α β (AE F E)) (c c' : ∀ w : InfinitePlace F, Matrix (Ix (P w) (Q w)) (Ix (R w) (S w)) ℂ), At (evI F) u → At (evI F) u' →
    (∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ) → (∀ w, u'.map (piInf (τ w)) = A w * c' w * (C w)ᵀ) →
    Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (evI F (symp (R := AF F) (cA σ) (-1) JA JB u u')) =
      -2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im := by
  first | exact @GlobalTheory.SympFramesD.symp_framesD | exact GlobalTheory.SympFramesD.symp_framesD | (intros; apply GlobalTheory.SympFramesD.symp_framesD <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicConstantTermParabolic
section
noncomputable section

open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open GlobalTheory.AutomorphicL2Unitary (LeftInv)
open GlobalTheory.Cusp (Cocompact constTermOn)
open scoped TensorProduct

namespace GlobalTheory.UAut.ConstAut

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem leftInv_foldr {Γ : Subgroup (GAd σ J)} {φ : GAd σ J → ℂ} (h : LeftInv Γ φ) :
    ∀ l : List (ℝ → GAd σ J), LeftInv Γ (l.foldr lineDer φ) := by
  intro l
  induction l with
  | nil => exact h
  | cons γ l ih =>
    intro x hx g
    simp only [List.foldr_cons, lineDer, mul_assoc, ih x hx]

theorem realLine_zero (h : IsCMExt F E σ) {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ) : γ 0 = 1 := by
  have e := isRealLine_add F E σ h n J γ hγ 0 0
  rw [add_zero] at e
  exact mul_left_cancel (e.symm.trans (mul_one _).symm)

theorem hasDerivAt_foldr (h : IsCMExt F E σ) {φ : GAd σ J → ℂ} (hs : IsSm σ J φ) {l : List (ℝ → GAd σ J)}
    (hl : ∀ γ ∈ l, IsRealLine σ J γ) {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ) (g : GAd σ J) (t : ℝ) :
    HasDerivAt (fun s => l.foldr lineDer φ (g * γ s)) ((γ :: l).foldr lineDer φ (g * γ t)) t := by
  have hd := (GlobalTheory.ThK.RealLineGrowthDerivative.differentiableAt_foldr_lineDer hs l hl hγ (g * γ t)).hasDerivAt
  have e : ∀ s, g * γ t * γ (s - t) = g * γ s := fun s => by
    rw [mul_assoc, ← isRealLine_add F E σ h n J γ hγ, add_sub_cancel]
  have h2 := HasDerivAt.comp_sub_const t t (by rw [sub_self]; exact hd)
  simp only [e] at h2
  exact h2

theorem isAutOn_constTerm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (C : Matrix (Fin n) (Fin r) E) (d : Fin r → ℕ), IsIsoCols σ J C → ∀ (H K : Subgroup (GAd σ J)) (φ c : GAd σ J → ℂ), ratPts σ J ⊓ parFlag σ J C d ≤ H → IsAutOn σ J H K φ → IsConstTermOn σ J (unipFlag σ J C d) φ c → IsAutOn σ J (leftGrp σ J C d) K c ∧ ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) → IsConstTermOn σ J (unipFlag σ J C d) (l.foldr lineDer φ) (l.foldr lineDer c) := by
  intro F E _ _ _ _ _ σ h n J hJ r C d hC H K φ c hH hφ hc
  classical
  haveI := locallyCompact_unipFlag hJ (sigma_sigma h) hC d
  have hφΓ : LeftInv (ratPts σ J ⊓ parFlag σ J C d) φ := fun γ hγ => hφ.left γ (hH hγ)
  obtain ⟨hco, e⟩ := hc.eq_constTermOn_par h hJ hC hφΓ
  have hcont : ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) → Continuous (l.foldr lineDer φ) :=
    GlobalTheory.T.continuous_iteratedRealLineDeriv_unitaryAdelic F E σ h n J hJ φ hφ.level hφ.cont hφ.smooth
  have hleft : ∀ l : List (ℝ → GAd σ J), LeftInv (ratPts σ J ⊓ parFlag σ J C d) (l.foldr lineDer φ) :=
    leftInv_foldr hφΓ
  have hder : ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) →
      l.foldr lineDer c = constTermOn (ratPts σ J ⊓ parFlag σ J C d) (unipFlag σ J C d) (l.foldr lineDer φ) := by
    intro l
    induction l with
    | nil => intro _; exact e
    | cons γ l ih =>
      intro hl
      have hl' : ∀ γ' ∈ l, IsRealLine σ J γ' := fun γ' h' => hl γ' (List.mem_cons_of_mem _ h')
      have hγ : IsRealLine σ J γ := hl γ List.mem_cons_self
      funext x
      have hx := GlobalTheory.CuspLie.hasDerivAt_constTermOn hco (hleft l) (hcont l hl') (hleft (γ :: l)) (hcont (γ :: l) hl)
        (GlobalTheory.RealLineCont.continuous_of_isRealLine F E σ h n J γ hγ) (hasDerivAt_foldr h hφ.smooth hl' hγ) x
      rw [realLine_zero h hγ, mul_one] at hx
      rw [List.foldr_cons, ih hl']
      exact hx.deriv
  have hct : ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) →
      IsConstTermOn σ J (unipFlag σ J C d) (l.foldr lineDer φ) (l.foldr lineDer c) := by
    intro l hl
    obtain ⟨c', hc', -⟩ := existsUnique_isConstTermOn h hJ hC d (φ := l.foldr lineDer φ)
      fun γ hγ => hleft l γ ⟨hγ.1, unipFlag_le_parFlag hJ (sigma_sigma h) hC d hγ.2⟩
    rwa [hder l hl, ← (hc'.eq_constTermOn_par h hJ hC (hleft l)).2]
  let S : Submodule ℂ (GAd σ J → ℂ) :=
    { carrier := {f | LeftInv (ratPts σ J ⊓ parFlag σ J C d) f ∧ Continuous f}
      add_mem' := fun ha hb => ⟨fun γ hγ g => by simp [ha.1 γ hγ g, hb.1 γ hγ g], ha.2.add hb.2⟩
      zero_mem' := ⟨fun _ _ _ => rfl, continuous_const⟩
      smul_mem' := fun a f hf => ⟨fun γ hγ g => by simp [hf.1 γ hγ g], hf.2.const_smul a⟩ }
  let Tl : S →ₗ[ℂ] (GAd σ J → ℂ) :=
    { toFun := fun f => constTermOn (ratPts σ J ⊓ parFlag σ J C d) (unipFlag σ J C d) f.1
      map_add' := fun a b => funext fun x => hco.constTermOn_add a.2.1 a.2.2 b.2.1 b.2.2 x
      map_smul' := fun a f => funext fun x => GlobalTheory.Cusp.constTermOn_smul a f.1 x }
  have hfin : ∀ W : Submodule ℂ (GAd σ J → ℂ), FiniteDimensional ℂ W →
      FiniteDimensional ℂ ((W.comap S.subtype).map Tl) := by
    intro W hW
    haveI : FiniteDimensional ℂ (W.comap S.subtype) := FiniteDimensional.of_injective
      (S.subtype.restrict (q := W) fun _ hx => hx) fun _ _ h => Subtype.ext (Subtype.ext (congrArg (fun z : W => z.1) h))
    infer_instance
  have hsum : ∀ (s : Finset (List (ℝ → GAd σ J))) (a : List (ℝ → GAd σ J) → ℂ),
      (∀ l ∈ s, ∀ γ ∈ l, IsRealLine σ J γ) →
      (∑ l ∈ s, a l • l.foldr lineDer φ) ∈ S ∧
      constTermOn (ratPts σ J ⊓ parFlag σ J C d) (unipFlag σ J C d) (∑ l ∈ s, a l • l.foldr lineDer φ) =
        ∑ l ∈ s, a l • constTermOn (ratPts σ J ⊓ parFlag σ J C d) (unipFlag σ J C d) (l.foldr lineDer φ) := by
    intro s a hs
    induction s using Finset.induction_on with
    | empty => exact ⟨S.zero_mem, funext fun x => by simp [GlobalTheory.Cusp.constTermOn]⟩
    | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      obtain ⟨h1, h2⟩ := ih fun l hl => hs l (Finset.mem_insert_of_mem hl)
      have m : a i • i.foldr lineDer φ ∈ S :=
        S.smul_mem _ ⟨hleft i, hcont i (hs i (Finset.mem_insert_self i s))⟩
      refine ⟨S.add_mem m h1, ?_⟩
      rw [← h2]
      funext x
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      rw [hco.constTermOn_add m.1 m.2 h1.1 h1.2 x, GlobalTheory.Cusp.constTermOn_smul]
  have hlevel : ∃ U : Subgroup (GAd σ J), IsOpen (U : Set (GAd σ J)) ∧
      ∀ k ∈ U, k ∈ finPts σ J → ∀ g, c (g * k) = c g := by
    obtain ⟨U, hU, hUk⟩ := hφ.level
    refine ⟨U, hU, fun k hk hf g => ?_⟩
    rw [e, ← GlobalTheory.Cusp.constTermOn_mul_right]
    exact congrArg (fun f => constTermOn _ _ f g) (funext fun y => hUk k hk hf y)
  have hkfin : GlobalTheory.Doubling.IsKFinite K c := by
    obtain ⟨W, hW, hWk⟩ := GlobalTheory.Doubling.isKFinite_iff.1 hφ.kfin
    refine GlobalTheory.Doubling.isKFinite_iff.2 ⟨_, hfin W hW, fun k hk => ⟨⟨fun g => φ (g * k),
      fun γ hγ g => by simp only [mul_assoc]; exact hφΓ γ hγ _, hφ.cont.comp (continuous_mul_right k)⟩,
      hWk k hk, funext fun g => ?_⟩⟩
    show constTermOn _ _ (fun g => φ (g * k)) g = c (g * k)
    rw [GlobalTheory.Cusp.constTermOn_mul_right, e]
  have hzfin : FiniteDimensional ℂ (Submodule.span ℂ {f | ∃ z, IsCentral σ J z ∧ f = dop z c}) := by
    haveI := hfin (Submodule.span ℂ {f | ∃ z, IsCentral σ J z ∧ f = dop z φ}) hφ.zfin
    refine Submodule.finiteDimensional_of_le
      (S₂ := ((Submodule.span ℂ {f | ∃ z, IsCentral σ J z ∧ f = dop z φ}).comap S.subtype).map Tl) (Submodule.span_le.2 ?_)
    rintro _ ⟨z, hz, rfl⟩
    have hr : ∀ l ∈ z.support, ∀ γ ∈ l, IsRealLine σ J γ := hz.1
    have hd1 : dop z φ = ∑ l ∈ z.support, z l • l.foldr lineDer φ := funext fun g => by
      simp [dop, Finsupp.sum, Finset.sum_apply]
    have hd2 : dop z c = ∑ l ∈ z.support, z l •
        constTermOn (ratPts σ J ⊓ parFlag σ J C d) (unipFlag σ J C d) (l.foldr lineDer φ) := funext fun g => by
      simp only [dop, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl fun l hl => by rw [hder l (hr l hl)]
    obtain ⟨m, hm⟩ := hsum z.support (fun l => z l) hr
    refine ⟨⟨_, m⟩, ?_, ?_⟩
    · show (∑ l ∈ z.support, z l • l.foldr lineDer φ) ∈ Submodule.span ℂ {f | ∃ z, IsCentral σ J z ∧ f = dop z φ}
      rw [← hd1]
      exact Submodule.subset_span ⟨z, hz, rfl⟩
    · show constTermOn _ _ _ = _
      rw [hm, hd2]
  have hgrowth : ∃ M : ℕ, ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) →
      ∃ B : ℝ, ∀ g, ‖l.foldr lineDer c g‖ ≤ B * (height σ J g : ℝ) ^ M := by
    obtain ⟨M, hM⟩ := hφ.growth
    obtain ⟨K0, hK0, hs⟩ := id hco
    haveI := hco.isProbabilityMeasure
    obtain ⟨A, hA⟩ := (hK0.image continuous_subtype_val).exists_bound_of_continuousOn
      (f := fun x => (height σ J x : ℝ)) (NNReal.continuous_coe.comp (continuous_height_GAd σ J)).continuousOn
    refine ⟨M, fun l hl => ?_⟩
    obtain ⟨B, hB⟩ := hM l hl
    refine ⟨max B 0 * max A 0 ^ M, fun g => ?_⟩
    have h1 : ∀ x : unipFlag σ J C d, ‖l.foldr lineDer φ ((x : GAd σ J) * g)‖ ≤
        max B 0 * (max A 0 * (height σ J g : ℝ)) ^ M := by
      intro x
      obtain ⟨γ, hγ, hk⟩ := hs x
      have e1 : l.foldr lineDer φ ((x : GAd σ J) * g) =
          l.foldr lineDer φ (((γ * x : unipFlag σ J C d) : GAd σ J) * g) := by
        rw [Subgroup.coe_mul, mul_assoc]; exact (hleft l _ hγ _).symm
      have e2 : (height σ J ((γ * x : unipFlag σ J C d) : GAd σ J) : ℝ) ≤ max A 0 := by
        have := hA _ ⟨_, hk, rfl⟩
        rw [Real.norm_eq_abs] at this
        exact (le_abs_self _).trans (this.trans (le_max_left _ _))
      have e3 : (height σ J (((γ * x : unipFlag σ J C d) : GAd σ J) * g) : ℝ) ≤ max A 0 * height σ J g :=
        calc (height σ J (((γ * x : unipFlag σ J C d) : GAd σ J) * g) : ℝ)
            ≤ height σ J ((γ * x : unipFlag σ J C d) : GAd σ J) * height σ J g := by
              exact_mod_cast height_mul_le σ J _ _
          _ ≤ max A 0 * height σ J g := mul_le_mul_of_nonneg_right e2 (NNReal.coe_nonneg _)
      rw [e1]
      calc _ ≤ B * (height σ J (((γ * x : unipFlag σ J C d) : GAd σ J) * g) : ℝ) ^ M := hB _
        _ ≤ max B 0 * (height σ J (((γ * x : unipFlag σ J C d) : GAd σ J) * g) : ℝ) ^ M :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg (NNReal.coe_nonneg _) _)
        _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (NNReal.coe_nonneg _) e3 _) (le_max_right _ _)
    rw [hder l hl]
    refine (norm_integral_le_of_norm_le_const (μ := GlobalTheory.Cusp.probMeasure _ _) (.of_forall fun q => h1 q.out)).trans
      (le_of_eq ?_)
    simp [mul_pow, mul_assoc]
  exact ⟨⟨hc.leftInv h hJ hC hφΓ, hlevel, hc.continuous h hJ hC hφΓ hφ.cont,
    GlobalTheory.T.constant_term_smooth_parabolic F E σ h n J hJ r C d hC H K φ c hH hφ hc, hgrowth, hkfin, hzfin⟩, hct⟩

end GlobalTheory.UAut.ConstAut

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcDensEqOfGram
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ChartGlue
open GlobalTheory.Twist (resM resM_resM resM_self app_resM)
open GlobalTheory.QCoh (pullbackSections)
open GlobalTheory.VBExt (AdaptedChart)
open ReciprocityTheory.L2DbarEstimates (V)
open Limits (cokernel)

namespace GlobalTheory

namespace Vert.Flag

variable {X Y : Scheme.{0}} {E : X.Modules} {N : ℕ} (fl : Flag E N) (π : Y ⟶ X)

def pull : Flag ((Scheme.Modules.pullback π).obj E) N where
  F i := (Scheme.Modules.pullback π).obj (fl.F i)
  ι i := (Scheme.Modules.pullback π).map (fl.ι i)
  isSubbundle i := SubPull.isSubbundle_pullback X Y π _ _ _ i (fl.isVB i) (fl.isSubbundle i)
  isVB i := (fl.isVB i).pullback π
  step i := (Scheme.Modules.pullback π).map (fl.step i)
  step_ι i := by rw [← Functor.map_comp, fl.step_ι]
  isIso_last := inferInstance

def pullGrIso (i : Fin N) : (Scheme.Modules.pullback π).obj (fl.gr i) ≅ (fl.pull π).gr i :=
  Limits.PreservesCokernel.iso (Scheme.Modules.pullback π) (fl.step i)

theorem map_π_pullGrIso (i : Fin N) :
    (Scheme.Modules.pullback π).map (fl.π i) ≫ (fl.pullGrIso π i).hom = (fl.pull π).π i := by
  have e := Limits.π_comp_cokernelComparison (fl.step i) (Scheme.Modules.pullback π)
  rw [← Limits.PreservesCokernel.iso_inv] at e
  have e' := congrArg (· ≫ (Limits.PreservesCokernel.iso (Scheme.Modules.pullback π) (fl.step i)).hom) e
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at e'
  exact e'.symm

end Vert.Flag

namespace VMetric

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {σ : k →+* ℂ}
  {E : X.Modules} {r : ℕ} (fl : Vert.Flag E r) (π : Y ⟶ X) (i : Fin r)

def pullStep (a : AdaptedChart (stepSeq fl i) i 1) : AdaptedChart (stepSeq (fl.pull π) i) i 1 :=
  have := (fl.isVB i.castSucc).isQuasicoherent
  have := (fl.isVB_gr i).isQuasicoherent
  { U := π ⁻¹ᵁ a.U
    e := fun j => pullbackSections π _ le_rfl (a.e j)
    t := fun j => pullbackSections π _ le_rfl (a.t j)
    he := a.he.pullback π
    ht := by
      have h := (a.ht.pullback π).map_iso (fl.pullGrIso π i).hom
      convert h using 2 with j
      rw [← QCoh.pullback_map_app_pullbackSections]
      exact (congr(($(fl.map_π_pullGrIso π i)).app _ _)).symm }

theorem pullStep_frame (a : AdaptedChart (stepSeq fl i) i 1) (j : Fin i ⊕ Fin 1) :
    (pullStep fl π i a).frame j = pullbackSections π _ le_rfl (a.frame j) := by
  have := ((fl.isVB i.succ)).isQuasicoherent
  rcases j with j | j
  · exact QCoh.pullback_map_app_pullbackSections π (fl.step i) _ _
  · rfl

variable {fl π i}

theorem gram_pullStep (h : VMetric p E r) (hπ : π ≫ p = q) (a : AdaptedChart (stepSeq fl i) i 1)
    {z : CxPts q σ} (hz : z ∈ ptsIn q σ (π ⁻¹ᵁ a.U)) :
    (((h.pull π hπ).stepMet (fl.pull π) i).met σ).gram (pullStep fl π i a).frame z =
      ((h.stepMet fl i).met σ).gram a.frame (PtsOver.map π hπ _ z) := by
  have hz' : PtsOver.map π hπ _ z ∈ ptsIn p σ a.U := hz
  ext j l
  change (((h.pull π hπ).met σ).restrict ((fl.pull π).isSubbundle i.succ)
    ((fl.pull π).isVB i.succ)).form _ _ z =
    ((h.met σ).restrict (fl.isSubbundle i.succ) (fl.isVB i.succ)).form _ _ _
  refine (Met.form_restrict _ _ _ _ _ hz).trans (Eq.trans ?_ (Met.form_restrict _ _ _ _ _ hz').symm)
  have e (j) : ((fl.pull π).ι i.succ).app (π ⁻¹ᵁ a.U) ((pullStep fl π i a).frame j) =
      pullbackSections π E le_rfl ((fl.ι i.succ).app a.U (a.frame j)) := by
    rw [pullStep_frame]
    exact QCoh.pullback_map_app_pullbackSections π _ _ _
  rw [e j, e l]
  exact Met.form_pull _ π hπ _ _ _ hz

theorem _root_.GlobalTheory.Met.bcDens_eq_of_gram {S : ShortComplex X.Modules} {S' : ShortComplex Y.Modules}
    {r s : ℕ} {h : Met p σ S.X₂ (r + s)} {h' : Met q σ S'.X₂ (r + s)} (hS : S.ShortExact)
    (hS' : S'.ShortExact) (h₁ : IsVB S.X₁ r) (h₃ : IsVB S.X₃ s) (h₁' : IsVB S'.X₁ r)
    (h₃' : IsVB S'.X₃ s) (H : h.IsCInf) (H' : h'.IsCInf) (a : AdaptedChart S r s)
    (a' : AdaptedChart S' r s) (c : AlgChart p σ 1) (c' : AlgChart q σ 1) {y : CxPts p σ}
    {z : CxPts q σ} (hy : y ∈ c.e.source) (hz : z ∈ c'.e.source) (ha : y ∈ ptsIn p σ a.U)
    (ha' : z ∈ ptsIn q σ a'.U) (he : c'.e z = c.e y)
    (hg : ∀ᶠ v in 𝓝 (c'.e z), h'.gram a'.frame (c'.e.symm v) = h.gram a.frame (c.e.symm v)) :
    h'.bcDens hS' h₁' h₃' c' z = h.bcDens hS h₁ h₃ c y := by
  rw [Met.bcDens_eq hS' h₁' h₃' a' c' H' hz ha', Met.bcDens_eq hS h₁ h₃ a c H hy ha, Met.bcForm,
    Met.bcForm, extTrace_congr hg, he]

theorem bcDens_pullStep {h : VMetric p E r} (H : h.IsCInf) (hπ : π ≫ p = q) (c : AlgChart p σ 1)
    (c' : AlgChart q σ 1) {z : CxPts q σ} (hz : z ∈ c'.e.source)
    (hz' : PtsOver.map π hπ _ z ∈ c.e.source)
    (he : ∀ w ∈ c'.e.source, PtsOver.map π hπ _ w ∈ c.e.source →
      c'.e w = c.e (PtsOver.map π hπ (spMap σ) w)) :
    (((h.pull π hπ).stepMet (fl.pull π) i).met σ).bcDens (stepSeq_shortExact (fl.pull π) i)
        ((fl.pull π).isVB i.castSucc) ((fl.pull π).isVB_gr i) c' z =
      ((h.stepMet fl i).met σ).bcDens (stepSeq_shortExact fl i) (fl.isVB i.castSucc)
        (fl.isVB_gr i) c (PtsOver.map π hπ _ z) := by
  obtain ⟨a, ha⟩ := Met.exists_adapted (stepSeq_shortExact fl i) (fl.isVB i.castSucc)
    (fl.isVB_gr i) (PtsOver.map π hπ _ z)
  have ha' : z ∈ ptsIn q σ (π ⁻¹ᵁ a.U) := ha
  have H₁ : (h.stepMet fl i).IsCInf := H.restrict _ _
  have H₂ : ((h.pull π hπ).stepMet (fl.pull π) i).IsCInf := (H.pull π hπ).restrict _ _
  have hm : Continuous (PtsOver.map π hπ (spMap σ)) := PtsOver.continuous_map π hπ _
  have hS : IsOpen (c'.e.source ∩ PtsOver.map π hπ (spMap σ) ⁻¹' (c.e.source ∩ ptsIn p σ a.U)) :=
    c'.e.open_source.inter ((c.e.open_source.inter (isOpen_ptsIn _)).preimage hm)
  have hn := (isOpen_over c'.e hS).mem_nhds (mem_over c'.e hz (S := _) ⟨hz, hz', ha⟩)
  refine Met.bcDens_eq_of_gram _ _ _ _ _ _ (H₁ σ) (H₂ σ) a (pullStep fl π i a) c c' hz' hz ha ha'
    (he z hz hz') ?_
  filter_upwards [hn] with v hv
  obtain ⟨h₁, h₂, h₃⟩ := hv.2
  have e₁ : c.e.symm v = PtsOver.map π hπ _ (c'.e.symm v) := by
    have := he _ h₁ h₂
    rw [c'.e.right_inv hv.1] at this
    exact (congrArg c.e.symm this).trans (c.e.left_inv h₂)
  rw [e₁]
  exact gram_pullStep h hπ a h₃

end VMetric

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockEmbeddingRationalGLMemRationalPoints
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open Matrix
open Formalism.UG (cT)
open scoped TensorProduct

namespace GlobalTheory.CuspBlockRat

theorem blockEmb_ratGL_mem_ratPts : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf →
    ∀ (l d : ℕ) (h : l + d ≤ r) (ι : GlobalTheory.CuspRep.GA E d →* GAd σ J), GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι →
      ∀ γ : GL (Fin d) E, ι (GlobalTheory.CuspRep.ratGL E d γ) ∈ ratPts σ J := by
  intro F E _ _ _ _ _ _ σ _ n J _ r Xf Yf _ l d h ι hι γ
  obtain ⟨Φ, j, -, -, hj, hΦ, hmat⟩ := hι
  have hΦE : ∀ x : E, Φ (inclR (F := F) (AF F) x) = algebraMap E (AdeleRing (𝓞 E) E) x := fun x => by
    rw [hΦ]
    refine Prod.ext ?_ ?_
    · show j (GlobalTheory.LFun.infTens F E ((1 : AF F) ⊗ₜ[F] x)) = algebraMap E (InfiniteAdeleRing E) x
      rw [← hj x]
      congr 1
    · show GlobalTheory.LFun.finAdEquiv F E (GlobalTheory.LFun.finTens F E ((1 : AF F) ⊗ₜ[F] x)) =
        algebraMap E (FiniteAdeleRing (𝓞 E) E) x
      have e : GlobalTheory.LFun.finTens F E ((1 : AF F) ⊗ₜ[F] x) = (1 : Af F) ⊗ₜ[F] x := by simp [GlobalTheory.LFun.finTens]
      rw [e, show GlobalTheory.LFun.finAdEquiv F E ((1 : Af F) ⊗ₜ[F] x) = _ from GlobalTheory.LFun.toFinAd_tmul 1 x, map_one, one_mul]
  have hΦs : ∀ x : E, Φ.symm (algebraMap E (AdeleRing (𝓞 E) E) x) = inclR (F := F) (AF F) x := fun x => by
    rw [RingEquiv.symm_apply_eq, hΦE]
  have hinj : Function.Injective (inclR (F := F) (E := E) (AF F)) := by
    intro x y hxy
    obtain ⟨w⟩ : Nonempty (InfinitePlace E) := inferInstance
    have := congrArg (fun z => (Φ z).1 w) hxy
    simp only [hΦE] at this
    exact (algebraMap E w.Completion).injective this
  have hrat : ∀ δ : GL (Fin d) E, (GlobalTheory.CuspRep.ratGL E d δ).1.map Φ.symm = δ.1.map (inclR (F := F) (AF F)) :=
    fun δ => by
      ext a b
      exact hΦs (δ.1 a b)
  refine GlobalTheory.CuspBlockLeft.mem_ratPts_of _ (1 + GlobalTheory.BlockForms.blkCols h Xf * (γ.1 - 1) *
      (cT (σ : E →+* E) (GlobalTheory.BlockForms.blkCols h Yf) * J) +
    GlobalTheory.BlockForms.blkCols h Yf * (cT (σ : E →+* E) (γ⁻¹).1 - 1) *
      (cT (σ : E →+* E) (GlobalTheory.BlockForms.blkCols h Xf) * J)) ?_ hinj
  rw [hmat, ← map_inv, hrat, hrat, GlobalTheory.CuspBlockLeft.cT_inclR]
  simp [Matrix.map_add, Matrix.map_sub, Matrix.map_mul, Matrix.map_one]

end GlobalTheory.CuspBlockRat

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CapelliKilledSmoothFunctionCentreOrbitFiniteDimeStatement
section
open NumberField MeasureTheory GlobalTheory.CuspRep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.capelliKilled_smoothFunction_centreOrbit_finiteDimensional : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (b : ℕ) (q : (E →+* ℂ) → ℂ → Polynomial ℂ), (∀ τ u, q τ u ≠ 0) → ∃ (X' : Set (Module.End ℂ (Sm E b) → ℂ)) (D : ℕ), X'.Finite ∧ ∀ ψ : Sm E b, (∀ τ u, Polynomial.aeval (cap τ u) (q τ u) ψ = 0) → FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E b) => z ψ) '' Zalg E b)) ∧ Module.finrank ℂ (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E b) => z ψ) '' Zalg E b)) ≤ D ∧ ∀ (χ' : Module.End ℂ (Sm E b) → ℂ) (u : Sm E b), u ∈ Submodule.span ℂ ((fun z : Module.End ℂ (Sm E b) => z ψ) '' Zalg E b) → u ≠ 0 → (∀ z ∈ Zalg E b, z u = χ' z • u) → ∃ χ ∈ X', ∀ z ∈ Zalg E b, χ' z = χ z := by
  first | exact @GlobalTheory.KilledFinCentre.centre_orbit_finite | exact GlobalTheory.KilledFinCentre.centre_orbit_finite | (intros; apply GlobalTheory.KilledFinCentre.centre_orbit_finite <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentraliserCompactPartLeIntegralAlmostAllStatement
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.centraliser_compactPart_le_integral_almostAll : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∀ γ : UE E n, γ.1.val.charpoly.Separable → ∀ᶠ w in cofinite, cptPart (twCent (MonoidHom.id (UL n w)) (locPt w γ)) ≤ KL n w := by
  first | exact @GlobalTheory.BCT.GoodCpt.main | exact GlobalTheory.BCT.GoodCpt.main | (intros; apply GlobalTheory.BCT.GoodCpt.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeEqOfRealUnitaryConjStatement
section
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.LevGeo
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covolume_eq_of_realUnitary_conj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X X' : Data E r) (hΨ : X'.Ψ = X.Ψ) (u : (E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ) (x0 : Frame X.Ψ r) (x0' : Frame X'.Ψ r) (FF : Set (V (nd X))) (FF' : Set (V (nd X'))), X'.Gm = X.Gm → X'.p0 = X.p0 → (∀ τ ∈ X.Ψ, gram τ X.Gm (u τ) = X.Gm.map τ) → (∀ γ ∈ X.Γ, ∃ γ' ∈ X'.Γ, ∀ τ ∈ X.Ψ, u τ * (γ : Matrix (Fin r) (Fin r) E).map τ = (γ' : Matrix (Fin r) (Fin r) E).map τ * u τ) → (∀ γ' ∈ X'.Γ, ∃ γ ∈ X.Γ, ∀ τ ∈ X.Ψ, u τ * (γ : Matrix (Fin r) (Fin r) E).map τ = (γ' : Matrix (Fin r) (Fin r) E).map τ * u τ) → IsOrth X x0 → IsOrth X' x0' → IsFundSet X x0 FF → IsFundSet X' x0' FF' → muF X x0 FF = muF X' x0' FF' := by
  first | exact @GlobalTheory.CovolConj.muF_eq_of_conj | exact GlobalTheory.CovolConj.muF_eq_of_conj | (intros; apply GlobalTheory.CovolConj.muF_eq_of_conj <;> assumption)
end

