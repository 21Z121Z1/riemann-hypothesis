import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0574
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0488
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0524
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.Bundle0006
import Development.AutomorphicArithmetic.CyclotomicBounds.DeRhamLattices.CrysLatticeBdRPlusActionCompat
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraRestrictionCuspidalProductSumSubset
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0308
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0553
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0575
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0541
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormSubLtOneOfFix
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0474
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BdRpToBdR
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.CrystallineMapLemmas
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0576
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisFilDvdEisensteinPowOnDiscStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.acris_fil_dvd_eisenstein_pow_on_disc : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (C : Core l) (γ : Per.Acris l →+* bk.DA bk.ρ₀), (∀ a : Ainf l, γ (algebraMap (Ainf l) (Per.Acris l) a) = bk.iA a) → (∀ x, ‖γ x‖ ≤ 1) → ∀ (m : ℕ) (y : Per.Acris l), C.j y ∈ Per.FilP l m → bk.iS bk.E ^ m ∣ γ y := by
  first | exact @GlobalTheory.AcrisDisc.main | exact GlobalTheory.AcrisDisc.main | (intros; apply GlobalTheory.AcrisDisc.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisRegularOfTensorInjStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bcris_regular_of_tensorInj : ∀ (l : ℕ) [Fact l.Prime] (C : Core l), C.TensorInj → C.Regular := by
  first | exact @GlobalTheory.MemLoc.regular_of_tensorInj | exact GlobalTheory.MemLoc.regular_of_tensorInj | (intros; apply GlobalTheory.MemLoc.regular_of_tensorInj <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BdRImageBcrisEqAinfHatCoordinates
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

open GlobalTheory.BKGal.HatVal in
private theorem gen {l : ℕ} [Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] [CompleteSpace K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) {ι : Type} [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : LocLat (Gl l) ℚ_[l] K O)
    (jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T) {W : Type} [AddCommGroup W] (Y : TW (OB l O) T →+ W)
    (act : OD l O →+ (W →+ W)) (hmul : ∀ x y w, act (x * y) w = act x (act y w)) (C : GlobalTheory.MemLoc.Core l)
    (hact : ∀ (b : OB l O) (y : OD l O), iotaO O C b = dRO l O y → ∀ z : TW (OB l O) T, Y (b • z) = act y (Y z))
    (n : ℕ) (s : Fin n → ZMod a → Ahat O K l e) (m : Fin n → P.MMl) (c : ZMod a → ι → Ahat O K l e)
    (hc : ∀ τ j, algebraMap (Ahat O K l e) (AhatE O K l e) (c τ j) =
      ∑ i, hat O l e (P.mxInv τ j i) * GlobalTheory.BKGal.JumpDR.hsum P s (fun k => (m k).1) τ i) :
    ∑ k, act (ϖ.iD t K (s k)) (Y (jB (toBcris t ϖ P (m k)))) =
      ∑ j, act (ϖ.iD t K (fun τ => c τ j)) (Y (jB (Pi.single j 1))) := by
  have hco := UpperTheory.KN.phiMod_coefficients_eq_sum_of_inverse_matrix l a e O K t ϖ ι P n s m c hc
  have h1 : ∀ k, Y (jB (toBcris t ϖ P (m k))) = ∑ j, act (ϖ.iD t K
      (fun τ => GlobalTheory.GalStep.hatR O (coordL P (invL l (S O K e)) (m k) j τ : K⟦X⟧)))
      (Y (jB (Pi.single j 1))) := by
    intro k
    have h2 : toBcris t ϖ P (m k) = ∑ j, ϖ.iB t K
        (coordL P (invL l (S O K e)) (m k) j) • (Pi.single j 1 : ι → OB l O) := by
      funext i
      rw [toBcris_apply, Finset.sum_apply, Finset.sum_eq_single i]
      · rw [Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
      · intro j _ hj
        rw [Pi.smul_apply, Pi.single_eq_of_ne hj.symm, smul_zero]
      · intro h
        exact absurd (Finset.mem_univ i) h
    rw [h2, map_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [jB.map_smul]
    exact hact _ _ (UpperTheory.KN.crisIncl_iB_eq_deRhamIncl_iD l a e O K t ϖ C _) _
  simp only [h1, hco, map_sum, map_mul, AddMonoidHom.finset_sum_apply, hmul]
  exact Finset.sum_comm

theorem _root_.GlobalTheory.T.bdR_image_bcris_eq_ainfHat_coordinates : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a], l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (jB : (ι → OB l ↥(OL LL)) ≃ₗ[OB l ↥(OL LL)] TW (OB l ↥(OL LL)) T) (Pl : LocPrime l) (AI : LocAinf l Pl) (Td : LocTied l Pl AI) (X : TW (OB l ↥(OL LL)) T →+ T.V ⊗[ℚ_[l]] Pl.R.BdR), (∀ (o : ↥(OL LL)) (b : Per.Bcris l) (x : ↥T.L.T), X ((o ⊗ₜ[ℤ_[l]] b) ⊗ₜ[↥(OL LL)] x) = ((o : ↥LL.1) • (x : T.V)) ⊗ₜ[ℚ_[l]] GlobalTheory.BKGal.JumpDR.cB Td b) → ∀ (A : OD l ↥(OL LL) →+ (T.V ⊗[ℚ_[l]] Pl.R.BdR →+ T.V ⊗[ℚ_[l]] Pl.R.BdR)), (∀ (o : ↥(OL LL)) (b : Per.BdRp l) (v : T.V) (c : Pl.R.BdR), A (o ⊗ₜ[ℤ_[l]] b) (v ⊗ₜ[ℚ_[l]] c) = ((o : ↥LL.1) • v) ⊗ₜ[ℚ_[l]] (GlobalTheory.BKGal.JumpDR.cD Td b * c)) → ∀ (n : ℕ) (s : Fin n → ZMod a → Ahat ↥(OL LL) ↥LL.1 l e) (m : Fin n → P.MMl) (c : ZMod a → ι → Ahat ↥(OL LL) ↥LL.1 l e), (∀ τ j, algebraMap (Ahat ↥(OL LL) ↥LL.1 l e) (AhatE ↥(OL LL) ↥LL.1 l e) (c τ j) = ∑ i, hat ↥(OL LL) l e (P.mxInv τ j i) * GlobalTheory.BKGal.JumpDR.hsum P s (fun k => (m k).1) τ i) → ∑ k, A (ϖ.iD (thetaW a LL) ↥LL.1 (s k)) (X (jB (toBcris (thetaW a LL) ϖ P (m k)))) = ∑ j, A (ϖ.iD (thetaW a LL) ↥LL.1 (fun τ => c τ j)) (X (jB (Pi.single j 1))) := by
  intro _ l _ a e _ _ ϖ LL _ _ _ ι _ _ P T jB Pl AI Td Y hY act hA n s m c hc
  obtain ⟨C⟩ := GlobalTheory.MemLoc.nonempty_core l
  exact gen (thetaW a LL) ϖ P T jB Y act (GlobalTheory.T.coeffDeRhamPlusAction_mul_one l LL T Pl AI Td act hA).1 C
    (UpperTheory.KN.crysLattice_bdRPlus_action_compat l LL T Pl AI Td Y hY act hA C) n s m c hc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BernsteinZelevinskyDerivativeHarishChandraProduct
section
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq
open scoped Classical

namespace GlobalTheory.GLq.Leibniz

variable {g : ℕ} [Fact g.Prime]

theorem wh_sum (ψ : AddChar (ZMod g) ℂ) {n : ℕ} {ι : Type} (s : Finset ι) (f : ι → Gn g n → ℂ) :
    wh ψ (fun x => ∑ j ∈ s, f j x) = ∑ j ∈ s, wh ψ (f j) := by
  unfold wh tr
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

theorem wh_const_mul (ψ : AddChar (ZMod g) ℂ) {n : ℕ} (c : ℂ) (f : Gn g n → ℂ) :
    wh ψ (fun x => c * f x) = c * wh ψ f := by
  unfold wh tr
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => by ring

theorem wh_mul_const (ψ : AddChar (ZMod g) ℂ) {n : ℕ} (c : ℂ) (f : Gn g n → ℂ) :
    wh ψ (fun x => f x * c) = wh ψ f * c := by
  unfold wh tr
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun x _ => by ring

theorem isClass_of_isChar {G : Type} [Group G] {χ : G → ℂ} (h : IsChar χ) : IsClass χ := by
  obtain ⟨V, hV⟩ := h
  intro x y
  rw [← hV, ← hV, FDRep.char_conj]

theorem isChar_of_isIrr {G : Type} [Group G] {χ : G → ℂ} (h : IsIrr χ) : IsChar χ := by
  obtain ⟨V, -, hV⟩ := h
  exact ⟨V, hV⟩

theorem wh_gl_zero (ψ : AddChar (ZMod g) ℂ) : wh ψ (fun _ : Gn g 0 => (1 : ℂ)) = 1 := by
  have hsub : ∀ x : Gn g 0, x = 1 := fun x => Units.ext (Subsingleton.elim _ _)
  have huniv : (Finset.univ : Finset (Gn g 0)) = {1} := by
    ext x
    simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
    exact hsub x
  have hP : IsUniUp ((1 : Gn g 0) : Mt g 0) := fun a _ => a.elim0
  unfold wh tr eU eDat
  rw [huniv, Finset.sum_singleton]
  rw [Finset.filter_singleton, if_pos hP, Finset.sum_singleton, Finset.card_singleton]
  simp

theorem degL_sort_map (L : List (Pc g)) (I : Finset (Fin L.length)) :
    degL ((I.sort (· ≤ ·)).map L.get) = ∑ j ∈ I, (L.get j).1 := by
  unfold degL
  rw [List.map_map]
  have := Finset.sort_eq I (· ≤ ·)
  rw [Finset.sum_eq_multiset_sum, ← this, Multiset.map_coe, Multiset.sum_coe]
  rfl

theorem degL_eq_sum (L : List (Pc g)) : degL L = ∑ j : Fin L.length, (L.get j).1 := by
  have h := degL_sort_map L Finset.univ
  rw [Fin.sort_univ, List.map_get_finRange] at h
  exact h

theorem mem_of_sort_map (L : List (Pc g)) (I : Finset (Fin L.length)) {p : Pc g}
    (hp : p ∈ (I.sort (· ≤ ·)).map L.get) : p ∈ L := by
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hp
  exact List.get_mem L j

theorem wh_hcL (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1) :
    ∀ L : List (Pc g), (∀ p ∈ L, IsCusp p.2 ∧ wh ψ p.2 = 1) → wh ψ (hcL L (degL L)) = 1 := by
  intro L
  induction L with
  | nil => intro _; exact wh_gl_zero ψ
  | cons p L ih =>
    intro hL
    have hp := hL p List.mem_cons_self
    have hL' : ∀ q ∈ L, IsCusp q.2 ∧ wh ψ q.2 = 1 := fun q hq => hL q (List.mem_cons_of_mem p hq)
    have hβ : IsClass (hcL L (degL L)) :=
      isClass_of_isChar (GlobalTheory.gl_list_product_perm_char g L L (degL L) rfl (fun q hq => isChar_of_isIrr (hL' q hq).1.2.1)).1
    have hα : IsClass p.2 := isClass_of_isChar (isChar_of_isIrr hp.1.2.1)
    have hdeg : degL (p :: L) = p.1 + degL L := by simp [degL]
    rw [hcL_cons]
    unfold hc
    rw [GlobalTheory.GLq.WhMul.wh_hcT g ψ hψ p.1 (degL L) (degL (p :: L)) hdeg]
    · simp_rw [wh_const_mul]
      rw [wh_mul_const, ih hL', hp.2, one_mul]
    · intro y x z
      simp only
      rw [hα]
    · intro x y z
      simp only
      rw [hβ]

theorem wh_hcL_of_deg (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1) (L : List (Pc g)) (n : ℕ) (hn : degL L = n)
    (hL : ∀ p ∈ L, IsCusp p.2 ∧ wh ψ p.2 = 1) : wh ψ (hcL L n) = 1 := by
  subst hn
  exact wh_hcL ψ hψ L hL

theorem main : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ), ψ ≠ 1 → ∀ (L : List (Pc g)) (n i : ℕ),
    degL L = n → i ≤ n → (∀ p ∈ L, IsCusp p.2 ∧ wh ψ p.2 = 1) →
      wh ψ (der ψ i (hcL L n)) = (((Finset.univ : Finset (Finset (Fin L.length))).filter
        (fun I => ∑ j ∈ I, (L.get j).1 = i)).card : ℂ) ∧ wh ψ (hcL L n) = 1 := by
  intro g _ ψ hψ L n i hn hi hL
  refine ⟨?_, wh_hcL_of_deg ψ hψ L n hn hL⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hi
  have hcusp : ∀ p ∈ L, IsCusp p.2 := fun p hp => (hL p hp).1
  have htot : ∑ j : Fin L.length, (L.get j).1 = i + k := by rw [← degL_eq_sum]; exact hn
  have hsub : ∀ (I : Finset (Fin L.length)), ∀ p ∈ (I.sort (· ≤ ·)).map L.get, IsCusp p.2 ∧ wh ψ p.2 = 1 :=
    fun I p hp => hL p (mem_of_sort_map L I hp)
  have hB : ∀ I ∈ (Finset.univ : Finset (Finset (Fin L.length))).filter (fun I => ∑ j ∈ I, (L.get j).1 = i),
      wh ψ (hcL ((Iᶜ.sort (· ≤ ·)).map L.get) k) = 1 := by
    intro I hI
    rw [Finset.mem_filter] at hI
    refine wh_hcL_of_deg ψ hψ _ k ?_ (hsub Iᶜ)
    rw [degL_sort_map]
    have := Finset.sum_compl_add_sum I (fun j => (L.get j).1)
    omega
  have hA : ∀ I ∈ (Finset.univ : Finset (Finset (Fin L.length))).filter (fun I => ∑ j ∈ I, (L.get j).1 = i),
      wh ψ (hcL ((I.sort (· ≤ ·)).map L.get) i) = 1 := by
    intro I hI
    rw [Finset.mem_filter] at hI
    exact wh_hcL_of_deg ψ hψ _ i (by rw [degL_sort_map]; exact hI.2) (hsub I)
  have key : ∀ b, b = k → ∀ h : Gn g i, wh ψ (res i b (hcL L (i + k)) h) =
      ∑ I ∈ (Finset.univ : Finset (Finset (Fin L.length))).filter (fun I => ∑ j ∈ I, (L.get j).1 = i),
        hcL ((I.sort (· ≤ ·)).map L.get) i h * wh ψ (hcL ((Iᶜ.sort (· ≤ ·)).map L.get) k) := by
    intro b hb h
    subst hb
    have hr : res i b (hcL L (i + b)) h = fun y => ∑ I ∈ (Finset.univ : Finset (Finset (Fin L.length))).filter
        (fun I => ∑ j ∈ I, (L.get j).1 = i),
          hcL ((I.sort (· ≤ ·)).map L.get) i h * hcL ((Iᶜ.sort (· ≤ ·)).map L.get) b y :=
      funext fun y => GlobalTheory.GLq.ResCuspProd.main g L i b hn hcusp h y
    rw [hr, wh_sum]
    exact Finset.sum_congr rfl fun I _ => wh_const_mul ψ _ _
  have hder : der ψ i (hcL L (i + k)) = fun h =>
      ∑ I ∈ (Finset.univ : Finset (Finset (Fin L.length))).filter (fun I => ∑ j ∈ I, (L.get j).1 = i),
        hcL ((I.sort (· ≤ ·)).map L.get) i h * wh ψ (hcL ((Iᶜ.sort (· ≤ ·)).map L.get) k) :=
    funext fun h => key (i + k - i) (by omega) h
  rw [hder, wh_sum, Finset.sum_congr rfl fun I hI => by rw [wh_mul_const, hA I hI, hB I hI, one_mul]]
  simp

end GlobalTheory.GLq.Leibniz
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinEnvelopeDvdPrimeOfAinfStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_envelope_dvd_prime_of_ainf : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (En : Env bk bk.prism (bk.toP bk.E) (bk.toP X)) (An : Env bk (ainfObj K) (bk.ev bk.E) (bk.ev X)) (q : Hom En.Q An.Q), q.comp En.inl = An.inl.comp bk.ι → q.comp En.inr = An.inr → ∀ x : En.Q.A, ((l : ℕ) : An.Q.A) ∣ q.f x → ((l : ℕ) : En.Q.A) ∣ x := by
  first | exact @GlobalTheory.BSP.envPush_dvd_l | exact GlobalTheory.BSP.envPush_dvd_l | (intros; apply GlobalTheory.BSP.envPush_dvd_l <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CauchyIdentitySchurFormalDegreeStatement
section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cauchy_identity_schur_formal_degree : ∀ {m n : ℕ} (hmn : m ≤ n) (α : Fin n → ℂ) (β : Fin m → ℂ) (d : ℕ),
    ∑ l ∈ GlobalTheory.JSW.antiParts m d, GlobalTheory.JSW.schurAt (GlobalTheory.JSW.padTo hmn l) α * GlobalTheory.JSW.schurAt l β =
      ∑ k ∈ Finset.Nat.antidiagonalTuple m d,
        ∏ j, MvPolynomial.eval₂ (Int.castRingHom ℂ) α (MvPolynomial.hsymm (Fin n) ℤ (k j)) * β j ^ (k j) := by
  first | exact @GlobalTheory.JSW.CauchyGlue.cauchy_formal | exact GlobalTheory.JSW.CauchyGlue.cauchy_formal | (intros; apply GlobalTheory.JSW.CauchyGlue.cauchy_formal <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoboundaryBcrisOfDualExponentialZero
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

namespace GlobalTheory.KerExpCrys

theorem finite_Ks {l : ℕ} [Fact l.Prime] (K : FinExt l) (j : ℕ) :
    FiniteDimensional ℚ_[l] (Ks K j) := by
  haveI := K.2
  haveI : FiniteDimensional ℚ_[l] (K0 K) :=
    Module.Finite.of_injective
      (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
      (IntermediateField.inclusion_injective (inf_le_left : K0 K ≤ K.1))
  have hf : {x : Om l | x ^ (l ^ j) = 1}.Finite := by
    refine (Polynomial.nthRootsFinset (l ^ j) (1 : Om l)).finite_toSet.subset fun x hx => ?_
    exact Finset.mem_coe.2 ((Polynomial.mem_nthRootsFinset
      (pow_pos (Fact.out : l.Prime).pos _) _).2 hx)
  haveI := hf.to_subtype
  haveI : FiniteDimensional ℚ_[l] (IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ (l ^ j) = 1}) :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  exact IntermediateField.finiteDimensional_sup _ _

theorem cob_cris_of_expStar_zero : ∀ (D : Formalism.BasicNotions.D7), adm2 D → ArchimedeanSignatureMatching D → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ), Lev l s → ∀ (e : ℕ) (z : GQ l → ℚ_[l]), ExpStar D.loc (Gj K s) e z 0 → ∃ x : (D.loc l).R.B, ∀ σ ∈ Gj K s, algebraMap ℚ_[l] (D.loc l).R.B (z σ) = (((D.loc l).χQ σ ^ (-(e : ℤ)) : ℚ_[l]ˣ) : ℚ_[l]) • (D.loc l).actQ σ x - x := by
  intro D h2 h4 l _ K s hs e z hz
  obtain ⟨hpos, hzero⟩ := GlobalTheory.T.dualExponential_kernel_cyclotomic_cocycles D h2 h4 l K s hs e z hz
  rcases Nat.eq_zero_or_pos e with he | he
  · have hI := hzero he
    subst he
    obtain ⟨⟨hc, -, hadd⟩, -⟩ := hz
    have hadd' : ∀ g h : ↥(GK (⟨Ks K s, finite_Ks K s⟩ : FinExt l)),
        z ((g * h : ↥(GK (⟨Ks K s, finite_Ks K s⟩ : FinExt l))) : GQ l) = z g + z h := by
      intro g h
      have := hadd g g.2 h h.2
      simpa using this
    have h1 : z 1 = 0 := by
      have := hadd' 1 1
      simpa using this
    obtain ⟨b, hb⟩ := GlobalTheory.UnramifiedCrys.exists_rat (D.locA l) (D.locT l)
      (⟨Ks K s, finite_Ks K s⟩ : FinExt l) (fun g => z g) hc.restrict hadd' (by
        intro g hg
        induction hg using Subgroup.closure_induction with
        | mem x hx => exact hI x x.2 hx
        | one => exact h1
        | mul x y _ _ hx hy => rw [hadd', hx, hy, add_zero]
        | inv x _ hx =>
          have := hadd' x x⁻¹
          rw [mul_inv_cancel, hx, zero_add] at this
          rw [← this]
          exact h1)
    refine ⟨b, fun σ hσ => ?_⟩
    have := hb ⟨σ, hσ⟩
    simpa using this.symm
  · obtain ⟨y, -, hy⟩ := hpos he
    refine ⟨algebraMap ℚ_[l] _ y, fun σ hσ => ?_⟩
    rw [hy σ hσ, map_sub, map_mul, Algebra.smul_def]
    congr 2
    rw [Algebra.algebraMap_eq_smul_one, map_smul, map_one]

end GlobalTheory.KerExpCrys
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoboundaryMemCocyclesOddPrimeStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coboundary_mem_cocycles_odd_prime : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (LL : FinExt l) (T : QLat LL) (b : TW (OB l ↥(OL LL)) T) (c : Gl l → T.V), IsCobOf (sQ l) T b c → c ∈ continuousCocycles T.ρ := by
  first | exact @GlobalTheory.CobCont.main | exact GlobalTheory.CobCont.main | (intros; apply GlobalTheory.CobCont.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComparisonMatrixExistsOnDiscStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.comparisonMatrix_exists_on_disc : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (ρ : ↥(GK K) → Matrix (Fin d) (Fin d) ℤ_[l]) (τ : Ainf l) (s : Seed bk d ρ τ) (ht : Height s) (B : Obj l ↥(OL K)) (u : B.A) (f g : Hom bk.prism B), ∃ ε : Matrix (Fin d) (Fin d) (Disc l u bk.ρ₀), ht.Rel u f g ε := by
  first | exact @GlobalTheory.BSP.Height.rel_exists | exact GlobalTheory.BSP.Height.rel_exists | (intros; apply GlobalTheory.BSP.Height.rel_exists <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoordEPowBasis
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BKGal.HatVal
open scoped GlobalTheory.BKGal.HatVal

noncomputable section

namespace GlobalTheory.BKGal.HatVal.BasisCoord

variable {l : ℕ} [Fact l.Prime] {O K : Type} [CommRing O] [Algebra ℤ_[l] O]
  [NormedField K] [NormedAlgebra ℚ_[l] K] [Algebra O K]
  {G : Type} [Group G] [TopologicalSpace G]

theorem tWincl_smul' {R R' : Type} [CommRing R] [CommRing R'] [Algebra O R] [Algebra O R'] (f : R →ₐ[O] R')
    (T : LocLat G ℚ_[l] K O) (r : R) (z : TW R T) : TWincl f T (r • z) = f r • TWincl f T z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | tmul s x =>
    simp only [TWincl, smul_tmul', TensorProduct.map_tmul, AlgHom.toLinearMap_apply, LinearMap.id_apply,
      smul_eq_mul, map_mul]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

end GlobalTheory.BKGal.HatVal.BasisCoord

open GlobalTheory.BKGal.HatVal.BasisCoord in

theorem GlobalTheory.BKGal.HatVal.coord_E_pow_basis : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T) (ε δ : OCb l), IsEps ε → δ ^ l = ε → ∀ j : ι, ∃ c : ι → OA l O, inclL t ϖ D.toPhiMod c = inclO l O (((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) ^ H) • (Pi.single j 1 : ι → OW l O) ∧ ∃ z : TW (OA l O) T, toB l O ((1 : O) ⊗ₜ[ℤ_[l]] (muOf δ ^ η)) • R.jB (fun i => toB l O (c i)) = TWincl (toB l O) T (((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) ^ H • z) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ η H D T R ε δ hε hδ j

  let ej : Vec K a ι := fun _ => Pi.single j 1
  have hej : ej ∈ D.toPhiMod.M := mem_tot.2 fun τ i => by
    by_cases h : i = j
    · subst h; simp only [ej, Pi.single_eq_same]; exact one_mem _
    · simp only [ej, Pi.single_eq_of_ne h]; exact zero_mem _
  have hL : E K l e ^ H • ej ∈ D.toPhiMod.L := D.lower _ hej
  obtain ⟨c, hc⟩ := toW_mem_LA t ϖ D.toPhiMod hL

  have hw : toW t ϖ D.toPhiMod ⟨ej, mem_ME_of_mem_M hej⟩ = (Pi.single j 1 : ι → OW l O) := by
    ext1 i
    rw [toW_apply]
    by_cases h : i = j
    · subst h
      rw [Pi.single_eq_same]
      convert map_one (ϖ.iW t K) using 1
      exact congrArg _ (funext fun τ => Subtype.ext (by simp [ej]))
    · rw [Pi.single_eq_of_ne h]
      convert map_zero (ϖ.iW t K) using 1
      exact congrArg _ (funext fun τ => Subtype.ext (by simp [ej, Pi.single_eq_of_ne h]))

  have hE : ϖ.iW t K (fun _ => ⟨E K l e ^ H, le_away _ _ (pow_mem (E_mem l e _) H)⟩) =
      inclO l O (((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) ^ H) := by
    have h1 := ϖ.iW_of_mem t K (fun _ => EIn l e (A O K) ^ H)
    have h2 : ϖ.iTot t K (fun _ => EIn l e (A O K) ^ H) = ((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) ^ H := by
      rw [show (fun _ : ZMod a => EIn l e (A O K) ^ H) = (fun _ => EIn l e (A O K)) ^ H from rfl, map_pow,
        PiSys.iTot_E t K ϖ]
    rw [h2] at h1
    rw [← h1]
    exact congrArg _ (funext fun τ => Subtype.ext (by simp [EIn]))
  have hwE : toW t ϖ D.toPhiMod ⟨E K l e ^ H • ej, mem_ME_of_mem_L hL⟩ =
      inclO l O (((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) ^ H) • (Pi.single j 1 : ι → OW l O) := by
    rw [toW_smul t ϖ D.toPhiMod (fun _ => ⟨E K l e ^ H, le_away _ _ (pow_mem (E_mem l e _) H)⟩)
      ⟨ej, mem_ME_of_mem_M hej⟩ _ (fun τ => rfl), hE, hw]
  have h1 : inclL t ϖ D.toPhiMod c =
      inclO l O (((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) ^ H) • (Pi.single j 1 : ι → OW l O) :=
    hc.trans hwE
  refine ⟨c, h1, ?_⟩

  obtain ⟨-, hK2, -, -⟩ := GlobalTheory.T.breuilKisin_lattice_exponents_ainf_comparison l a e O K t ϖ ι D.toPhiMod T R.I η H D.upper D.lower ε δ hε hδ
  have hv : (Pi.single j 1 : ι → OW l O) ∈ MA D.toPhiMod :=
    ⟨Pi.single j 1, funext fun i => by
      by_cases h : i = j
      · subst h; simp [inclV]
      · simp [inclV, Pi.single_eq_of_ne h]⟩
  obtain ⟨z, hz⟩ := hK2 _ hv
  refine ⟨z, ?_⟩
  set m : OA l O := (1 : O) ⊗ₜ[ℤ_[l]] (muOf δ ^ η) with hm
  set Eh : OA l O := ((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e) : OA l O) ^ H with hEh
  have hB := R.cmp (fun i => m * c i) (Eh • z) (by
    rw [inclL_smul_coord, h1, smul_comm, map_smul, hz, tWincl_smul'])
  have e1 : (fun i => toB l O (m * c i)) = toB l O m • fun i => toB l O (c i) :=
    funext fun i => by simp only [map_mul, Pi.smul_apply, smul_eq_mul]
  rw [e1, map_smul] at hB
  exact hB
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DDeRhamEqDCrisOfUnramifiedStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions Formalism.MainNotions.N
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dDeRham_eq_dCris_of_unramified : ∀ D : D7, Formalism.MainNotions.TruncatedSeriesCountingBounds.adm15 D := by
  first | exact @GlobalTheory.FontaineAdmissibility.intersectionNumber_baseChange | exact GlobalTheory.FontaineAdmissibility.intersectionNumber_baseChange | (intros; apply GlobalTheory.FontaineAdmissibility.intersectionNumber_baseChange <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DcrisStrictHodgeFiltrationUnramifiedStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dcris_strict_hodgeFiltration_unramified : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l), Function.Bijective (algebraMap ↥(K0 K) ↥K.1) → ∀ (V₁ : Type) [AddCommGroup V₁] [Module ↥LL.1 V₁] [Module ℚ_[l] V₁] [IsScalarTower ℚ_[l] ↥LL.1 V₁] [FiniteDimensional ↥LL.1 V₁] (ρ₁ : Representation ↥LL.1 ↥(GK K) V₁) (V₂ : Type) [AddCommGroup V₂] [Module ↥LL.1 V₂] [Module ℚ_[l] V₂] [IsScalarTower ℚ_[l] ↥LL.1 V₂] [FiniteDimensional ↥LL.1 V₂] (ρ₂ : Representation ↥LL.1 ↥(GK K) V₂) (π : V₁ →ₗ[↥LL.1] V₂), (∀ g x, π (ρ₁ g x) = ρ₂ g (π x)) → (Function.Surjective π → IsCrys (P.PD K) ρ₁ → ∀ a : ℤ, (FilCris (P.PD K) ρ₁ a).map (AlgebraTensorModule.map π (LinearMap.id : P.R.B →ₗ[ℚ_[l]] P.R.B)) = FilCris (P.PD K) ρ₂ a) ∧ (Function.Injective π → ∀ a : ℤ, ∀ y ∈ Dcris (P.PD K) ρ₁, AlgebraTensorModule.map π (LinearMap.id : P.R.B →ₗ[ℚ_[l]] P.R.B) y ∈ FilCris (P.PD K) ρ₂ a → y ∈ FilCris (P.PD K) ρ₁ a) := by
  first | exact @GlobalTheory.Per.CrisStrict.dcris_strict | exact GlobalTheory.Per.CrisStrict.dcris_strict | (intros; apply GlobalTheory.Per.CrisStrict.dcris_strict <;> assumption)
end

