import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0108
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.MapHComp
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableHermC
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0104
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0109
import Formalism.RealPlaceAnalysis.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0227
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0045
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0091
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0098

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PermutationMatrixPropertiesStatement
section
open ReciprocityTheory.Ty.Fin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.permutation_matrix_properties : ReciprocityTheory.Ty.Fin.St.PmFacts := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.Pm.pmFacts | exact GlobalTheory.CompanionTheory.TyFin.Pm.pmFacts | (intros; apply GlobalTheory.CompanionTheory.TyFin.Pm.pmFacts <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PiHBijective
section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH

universe w w' w'' t t' v u v' u' v'' u''

namespace GlobalTheory.CompanionTheory.CatCohProd

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {ι : Type w}

def tup (F : ι → (C ⥤ ModuleCat.{w} R)) (n : ℕ) (g : ∀ i, Cn (F i) n) : Cn (piF F) n :=
  fun s i => g i s

theorem pull_tup (F : ι → (C ⥤ ModuleCat.{w} R)) (n : ℕ) (g : ∀ i, Cn (F i) n) (i : ι) :
    (piProj F i).pullC n (tup F n g) = g i := rfl

theorem cochain_ext (F : ι → (C ⥤ ModuleCat.{w} R)) (n : ℕ) {a b : Cn (piF F) n}
    (h : ∀ i, (piProj F i).pullC n a = (piProj F i).pullC n b) : a = b :=
  funext fun s => funext fun i => congrFun (h i) s

theorem pull_d (F : ι → (C ⥤ ModuleCat.{w} R)) (n : ℕ) (a : Cn (piF F) n) (i : ι) :
    (piProj F i).pullC (n + 1) (d (piF F) n a) = d (F i) n ((piProj F i).pullC n a) :=
  ((piProj F i).d_pullC n a).symm

theorem piH_bijective : ∀ {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {ι : Type w}
    (F : ι → (C ⥤ ModuleCat.{w} R)) (n : ℕ),
    Function.Bijective fun (x : H (piF F) n) (i : ι) => (piProj F i).pull n x := by
  intro R _ C _ ι F n
  have hz : ∀ (i : ι) (a : Cn (piF F) n), d (piF F) n a = 0 →
      d (F i) n ((piProj F i).pullC n a) = 0 := fun i a ha => by
    rw [← pull_d, ha, map_zero]
  constructor
  · intro x y hxy
    obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (cx (piF F)) n).1 x
    obtain ⟨b, hb, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (cx (piF F)) n).1 y
    have hi : ∀ i, (piProj F i).pullC n a - (piProj F i).pullC n b ∈ (cx (F i)).B n := fun i => by
      have h := congrFun hxy i
      have h' : (cx (F i)).cls ((piProj F i).pullC n a) (hz i a ha) =
          (cx (F i)).cls ((piProj F i).pullC n b) (hz i b hb) := h
      exact ((CrystallineSemistableComparison.P.cls_surj (cx (F i)) n).2.2.1 _ _ _ _).1 h'
    refine ((CrystallineSemistableComparison.P.cls_surj (cx (piF F)) n).2.2.1 a b ha hb).2 ?_
    cases n with
    | zero =>
      have h0 : a - b = 0 := by
        refine cochain_ext F 0 fun i => ?_
        rw [map_sub, map_zero]
        exact hi i
      rw [h0]
      exact Submodule.zero_mem _
    | succ n =>
      have hi' : ∀ i, ∃ c : Cn (F i) n, d (F i) n c =
          (piProj F i).pullC (n + 1) a - (piProj F i).pullC (n + 1) b := hi
      choose c hc using hi'
      refine ⟨tup F n c, cochain_ext F (n + 1) fun i => ?_⟩
      change (piProj F i).pullC (n + 1) (d (piF F) n (tup F n c)) = _
      rw [pull_d, pull_tup, hc, map_sub]
  · intro y
    have hy : ∀ i, ∃ (a : Cn (F i) n) (ha : d (F i) n a = 0), y i = (cx (F i)).cls a ha :=
      fun i => (CrystallineSemistableComparison.P.cls_surj (cx (F i)) n).1 (y i)
    choose a ha e using hy
    have hd : d (piF F) n (tup F n a) = 0 := by
      refine cochain_ext F (n + 1) fun i => ?_
      rw [pull_d, pull_tup, ha, map_zero]
    refine ⟨(cx (piF F)).cls (tup F n a) hd, funext fun i => ?_⟩
    rw [e i]
    rfl

end GlobalTheory.CompanionTheory.CatCohProd
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PqBaseChangePolynomial
section
open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.Perfection

theorem pq_baseChange_polynomial : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A](B : Type) [CommRing B] [Algebra A B] (K : Type) [CommRing K] [Algebra A K] (i : Polynomial A →ₐ[A] B) (h : Polynomial A), Pf p A → Pf p K → PQ p (i : Polynomial A →+* B) (Ideal.span {h}) → ∃ i₁ : Polynomial K →+* B ⊗[A] K, PQ p i₁ (Ideal.span {h.map (algebraMap A K)}) ∧ (∀ a, i₁ (Polynomial.C a) = (1 : B) ⊗ₜ[A] a) ∧ i₁ Polynomial.X = i Polynomial.X ⊗ₜ[A] (1 : K) := by
  intro p _ A _ B _ _ K _ _ i h hA hK hPQ
  let i₁ : Polynomial K →+* B ⊗[A] K :=
    Polynomial.eval₂RingHom (Algebra.TensorProduct.includeRight : K →ₐ[A] B ⊗[A] K).toRingHom
      (i Polynomial.X ⊗ₜ[A] (1 : K))
  have hC : ∀ a, i₁ (Polynomial.C a) = (1 : B) ⊗ₜ[A] a := by
    intro a
    simp [i₁]
  have hX : i₁ Polynomial.X = i Polynomial.X ⊗ₜ[A] (1 : K) := by
    simp [i₁]
  have hj : ∀ s : Polynomial A, i₁ (Polynomial.mapRingHom (algebraMap A K) s) = i s ⊗ₜ[A] (1 : K) := by
    intro s
    induction s using Polynomial.induction_on with
    | C a =>
      have h1 : i (Polynomial.C a) = algebraMap A B a := by
        rw [← Polynomial.algebraMap_eq]
        exact i.commutes a
      rw [Polynomial.coe_mapRingHom, Polynomial.map_C, hC, h1, Algebra.algebraMap_eq_smul_one,
        Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
    | add f g hf hg =>
      rw [map_add, map_add, hf, hg, map_add, TensorProduct.add_tmul]
    | monomial n a ih =>
      have e : (Polynomial.C a * Polynomial.X ^ (n + 1) : Polynomial A)
          = (Polynomial.C a * Polynomial.X ^ n) * Polynomial.X := by ring
      rw [e, map_mul, map_mul, ih, map_mul]
      have e2 : Polynomial.mapRingHom (algebraMap A K) (Polynomial.X : Polynomial A) = Polynomial.X := by
        simp
      rw [e2, hX, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      simp only [map_mul]
  have hcl : Subring.closure (Set.range (Polynomial.C : K →+* Polynomial K) ∪
      Set.range (Polynomial.mapRingHom (algebraMap A K))) = ⊤ := by
    rw [eq_top_iff]
    intro f _
    induction f using Polynomial.induction_on with
    | C a => exact Subring.subset_closure (Or.inl ⟨a, rfl⟩)
    | add f g hf hg => exact Subring.add_mem _ (hf trivial) (hg trivial)
    | monomial n a ih =>
      have e : (Polynomial.C a * Polynomial.X ^ (n + 1) : Polynomial K)
          = (Polynomial.C a * Polynomial.X ^ n) * Polynomial.X := by ring
      rw [e]
      refine Subring.mul_mem _ (ih trivial) (Subring.subset_closure (Or.inr ⟨Polynomial.X, ?_⟩))
      simp
  have hcomp : (Polynomial.C : K →+* Polynomial K).comp (algebraMap A K)
      = (Polynomial.mapRingHom (algebraMap A K)).comp (algebraMap A (Polynomial A)) := by
    ext a
    simp [Polynomial.algebraMap_apply]
  have key := GlobalTheory.T.perfect_tensor_generated_lift p A (Polynomial A) B K (Polynomial K) i (Ideal.span {h})
    Polynomial.C (Polynomial.mapRingHom (algebraMap A K)) i₁ hA hK hPQ hcomp hcl hC hj
  refine ⟨i₁, ?_, hC, hX⟩
  rw [Ideal.map_span, Set.image_singleton] at key
  simpa using key

end GlobalTheory.CompanionTheory.Perfection
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductHuaDeterminantIntegrable
section
open MeasureTheory
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch

namespace GlobalTheory.CompanionTheory.SiegelND.Integ.Arch

theorem integrable_prod_detW_rpow : ∀ (W : Type) [Fintype W] (n : ℕ) (s : ℝ), (n : ℝ) - 1 / 2 < s →
    ∀ ν : Measure (W → hermC n), ν.IsAddHaarMeasure →
    Integrable (fun b : W → hermC n => ∏ w, detW (b w : Matrix (Fin n) (Fin n) ℂ) ^ (-s)) ν := by
  intro W _ n s hs ν hν
  let μ₀ : Measure (hermC n) := Measure.addHaar
  have hf : ∀ _w : W, Integrable (fun b : hermC n => detW (b : Matrix (Fin n) (Fin n) ℂ) ^ (-s)) μ₀ :=
    fun _ => GlobalTheory.T.hua_determinant_integrable_of_lt n s hs μ₀ inferInstance
  have hpi := Integrable.fintype_prod (μ := fun _ : W => μ₀)
    (f := fun _ : W => fun b : hermC n => detW (b : Matrix (Fin n) (Fin n) ℂ) ^ (-s)) hf
  rw [Measure.isAddLeftInvariant_eq_smul ν (Measure.pi fun _ : W => μ₀)]
  exact hpi.smul_measure_nnreal

end GlobalTheory.CompanionTheory.SiegelND.Integ.Arch
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductSimpleAll
section
open ReciprocityTheory.Ty.Fin CategoryTheory

noncomputable section

namespace GlobalTheory.CompanionTheory.ProdSimple

def cf {Γ : Type} [Group Γ] (g : Γ) : MonoidAlgebra ℂ Γ →ₗ[ℂ] ℂ where
  toFun a := a.coeff g
  map_add' a b := by simp
  map_smul' r a := by simp

theorem cf_apply {Γ : Type} [Group Γ] (g : Γ) (a : MonoidAlgebra ℂ Γ) : cf g a = a.coeff g := rfl

def regSub {Γ : Type} [Group Γ] (N : Submodule ℂ (MonoidAlgebra ℂ Γ))
    (h : ∀ g : Γ, ∀ a ∈ N, MonoidAlgebra.single g (1 : ℂ) * a ∈ N) : Representation ℂ Γ N where
  toFun g := (LinearMap.mulLeft ℂ (MonoidAlgebra.single g (1 : ℂ))).restrict (h g)
  map_one' := by
    ext a
    simp [← MonoidAlgebra.one_def]
  map_mul' g k := by
    refine LinearMap.ext fun a => Subtype.ext ?_
    change MonoidAlgebra.single (g * k) (1 : ℂ) * (a : MonoidAlgebra ℂ Γ) =
      MonoidAlgebra.single g (1 : ℂ) * (MonoidAlgebra.single k (1 : ℂ) * (a : MonoidAlgebra ℂ Γ))
    rw [← mul_assoc, MonoidAlgebra.single_mul_single, one_mul]

theorem exists_irr {Γ : Type} [Group Γ] [Fintype Γ] {W : Type} [AddCommGroup W] [Module ℂ W]
    (T : MonoidAlgebra ℂ Γ →ₗ[ℂ] W) (hT : T 1 ≠ 0) :
    ∃ (N : Submodule ℂ (MonoidAlgebra ℂ Γ))
      (h : ∀ g : Γ, ∀ a ∈ N, MonoidAlgebra.single g (1 : ℂ) * a ∈ N),
      IsIrr (regSub N h) ∧ ∃ n ∈ N, T n ≠ 0 := by
  classical
  have htop := IsSemisimpleModule.sSup_simples_eq_top (MonoidAlgebra ℂ Γ) (MonoidAlgebra ℂ Γ)
  have hex : ∃ I : Submodule (MonoidAlgebra ℂ Γ) (MonoidAlgebra ℂ Γ),
      IsSimpleModule (MonoidAlgebra ℂ Γ) I ∧ ∃ n ∈ I, T n ≠ 0 := by
    by_contra hno
    push Not at hno
    have hz : ∀ a ∈ sSup {m : Submodule (MonoidAlgebra ℂ Γ) (MonoidAlgebra ℂ Γ) |
        IsSimpleModule (MonoidAlgebra ℂ Γ) m}, T a = 0 := by
      intro a ha
      rw [sSup_eq_iSup'] at ha
      refine Submodule.iSup_induction _ (motive := fun x => T x = 0) ha ?_ (map_zero T) ?_
      · rintro ⟨I, hI⟩ x hx
        exact hno I hI x hx
      · intro x y hx hy
        rw [map_add, hx, hy, add_zero]
    exact hT (hz 1 (by rw [htop]; trivial))
  obtain ⟨I, hI, n, hn, hTn⟩ := hex
  have hstab : ∀ g : Γ, ∀ a ∈ I.restrictScalars ℂ,
      MonoidAlgebra.single g (1 : ℂ) * a ∈ I.restrictScalars ℂ := fun g a ha =>
    I.smul_mem (MonoidAlgebra.single g (1 : ℂ)) ha
  refine ⟨I.restrictScalars ℂ, hstab, ⟨?_, ?_⟩, n, hn, hTn⟩
  · have hn0 : n ≠ 0 := fun h0 => hTn (by rw [h0, map_zero])
    exact ⟨⟨⟨n, hn⟩, 0, fun h0 => hn0 (congrArg Subtype.val h0)⟩⟩
  · intro U hU

    have hmul : ∀ a : MonoidAlgebra ℂ Γ, ∀ x ∈ U.map (I.restrictScalars ℂ).subtype,
        a * x ∈ U.map (I.restrictScalars ℂ).subtype := by
      intro a
      induction a using MonoidAlgebra.induction_on with
      | of g =>
        rintro x ⟨u, hu, rfl⟩
        exact ⟨regSub _ hstab g u, hU g u hu, rfl⟩
      | add a b ha hb =>
        intro x hx
        rw [add_mul]
        exact Submodule.add_mem _ (ha x hx) (hb x hx)
      | smul r a ha =>
        intro x hx
        rw [smul_mul_assoc]
        exact Submodule.smul_mem _ r (ha x hx)
    let J : Submodule (MonoidAlgebra ℂ Γ) (MonoidAlgebra ℂ Γ) :=
      { carrier := U.map (I.restrictScalars ℂ).subtype
        add_mem' := fun ha hb => Submodule.add_mem _ ha hb
        zero_mem' := Submodule.zero_mem _
        smul_mem' := fun a x hx => hmul a x hx }
    have hJI : J ≤ I := by
      rintro x ⟨u, -, rfl⟩
      exact u.2
    rcases (isSimpleModule_iff_isAtom.mp hI).le_iff.mp hJI with h0 | h1
    · left
      rw [eq_bot_iff]
      intro u hu
      have : (u : MonoidAlgebra ℂ Γ) ∈ J := ⟨u, hu, rfl⟩
      rw [h0] at this
      exact (Submodule.mem_bot ℂ).2 (Subtype.ext ((Submodule.mem_bot _).1 this))
    · right
      rw [eq_top_iff]
      intro u _
      have : (u : MonoidAlgebra ℂ Γ) ∈ J := by
        rw [h1]
        exact u.2
      obtain ⟨u', hu', he⟩ := this
      have : u' = u := Subtype.ext he
      exact this ▸ hu'

variable {s : ℕ} {L : Fin s → Type} [∀ c, Group (L c)] [∀ c, Fintype (L c)]
  {W : Type} [AddCommGroup W] [Module ℂ W]

def psi (ρ : Representation ℂ (∀ c, L c) W) (v : W) :
    MultilinearMap ℂ (fun c => MonoidAlgebra ℂ (L c)) W :=
  ∑ g : ∀ c, L c,
    ((MultilinearMap.mkPiAlgebra ℂ (Fin s) ℂ).compLinearMap (fun c => cf (g c))).smulRight (ρ g v)

theorem psi_apply (ρ : Representation ℂ (∀ c, L c) W) (v : W) (x : ∀ c, MonoidAlgebra ℂ (L c)) :
    psi ρ v x = ∑ g : ∀ c, L c, (∏ c, (x c).coeff (g c)) • ρ g v := by
  simp [psi, MultilinearMap.sum_apply, cf_apply]

theorem psi_one (ρ : Representation ℂ (∀ c, L c) W) (v : W) :
    psi ρ v (fun _ => 1) = v := by
  classical
  rw [psi_apply, Finset.sum_eq_single (1 : ∀ c, L c)]
  · simp [MonoidAlgebra.one_def]
  · intro g _ hg
    obtain ⟨c, hc⟩ : ∃ c, g c ≠ 1 := by
      by_contra hall
      push Not at hall
      exact hg (funext hall)
    rw [Finset.prod_eq_zero (Finset.mem_univ c), zero_smul]
    simp [MonoidAlgebra.one_def, Finsupp.single_apply, hc.symm]
  · simp

theorem psi_single_mul (ρ : Representation ℂ (∀ c, L c) W) (v : W) (g : ∀ c, L c)
    (x : ∀ c, MonoidAlgebra ℂ (L c)) :
    psi ρ v (fun c => MonoidAlgebra.single (g c) (1 : ℂ) * x c) = ρ g (psi ρ v x) := by
  rw [psi_apply, psi_apply, map_sum]
  refine Fintype.sum_equiv (Equiv.mulLeft g⁻¹) _ _ fun h => ?_
  simp only [MonoidAlgebra.coeff_single_mul_apply, one_mul, map_smul, Equiv.coe_mulLeft,
    Pi.mul_apply, Pi.inv_apply]
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]

theorem exists_family (ρ : Representation ℂ (∀ c, L c) W) (v : W) (hv : v ≠ 0) :
    ∃ x : ∀ c, MonoidAlgebra ℂ (L c),
      (∀ c, ∃ (N : Submodule ℂ (MonoidAlgebra ℂ (L c)))
        (h : ∀ g : L c, ∀ a ∈ N, MonoidAlgebra.single g (1 : ℂ) * a ∈ N),
        IsIrr (regSub N h) ∧ x c ∈ N) ∧ psi ρ v x ≠ 0 := by
  have key : ∀ S : Finset (Fin s), ∃ x : ∀ c, MonoidAlgebra ℂ (L c), (∀ c, c ∉ S → x c = 1) ∧
      (∀ c ∈ S, ∃ (N : Submodule ℂ (MonoidAlgebra ℂ (L c)))
        (h : ∀ g : L c, ∀ a ∈ N, MonoidAlgebra.single g (1 : ℂ) * a ∈ N),
        IsIrr (regSub N h) ∧ x c ∈ N) ∧ psi ρ v x ≠ 0 := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
      exact ⟨fun _ => 1, fun _ _ => rfl, by simp, by rwa [psi_one]⟩
    | insert c S hc ih =>
      obtain ⟨x, h1, h2, h3⟩ := ih
      have hT : (psi ρ v).toLinearMap x c 1 ≠ 0 := by
        rw [MultilinearMap.toLinearMap_apply, ← h1 c hc, Function.update_eq_self]
        exact h3
      obtain ⟨N, h, hirr, n, hn, hTn⟩ := exists_irr _ hT
      refine ⟨Function.update x c n, fun c' hc' => ?_, fun c' hc' => ?_, ?_⟩
      · rw [Finset.mem_insert, not_or] at hc'
        rw [Function.update_of_ne hc'.1]
        exact h1 c' hc'.2
      · by_cases hcc : c' = c
        · subst hcc
          exact ⟨N, h, hirr, by rwa [Function.update_self]⟩
        · obtain ⟨N', h', hirr', hm⟩ := h2 c' ((Finset.mem_insert.mp hc').resolve_left hcc)
          exact ⟨N', h', hirr', by rwa [Function.update_of_ne hcc]⟩
      · simpa [MultilinearMap.toLinearMap_apply] using hTn
  obtain ⟨x, -, h2, h3⟩ := key Finset.univ
  exact ⟨x, fun c => h2 c (Finset.mem_univ c), h3⟩

end GlobalTheory.CompanionTheory.ProdSimple

open GlobalTheory.CompanionTheory.ProdSimple in
theorem GlobalTheory.CompanionTheory.ProdSimple.prodSimpleAll : ReciprocityTheory.Ty.Fin.St.ProdSimpleAll := by
  intro s L _ _ W _ _ _ _ ρ
  obtain ⟨v, hv⟩ := exists_ne (0 : W)
  obtain ⟨x, hx, hne⟩ := exists_family ρ v hv
  choose N h hirr hmem using hx
  have hfin : ∀ c, Module.Finite ℂ (N c) := fun c => inferInstance
  let lam : ∀ c, FDRep ℂ (L c) := fun c => FDRep.of (regSub (N c) (h c))
  let M : MultilinearMap ℂ (fun c => (lam c : Type)) W :=
    (psi ρ v).compLinearMap (fun c => (N c).subtype)
  refine ⟨lam, PiTensorProduct.lift M, fun c => ?_, ?_, fun g => ?_⟩
  · exact (GlobalTheory.CompanionTheory.TyFin.simpleIffIrr.1 (L c) (lam c)).2 (hirr c)
  · intro h0
    apply hne
    have := congrArg (fun f => f (PiTensorProduct.tprod ℂ (fun c => (⟨x c, hmem c⟩ : N c)))) h0
    simp only [LinearMap.zero_apply, PiTensorProduct.lift.tprod] at this
    exact this
  · apply PiTensorProduct.ext
    ext y
    simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, PiTensorProduct.map_tprod,
      PiTensorProduct.lift.tprod]
    exact psi_single_mul ρ v g (fun c => (y c : MonoidAlgebra ℂ (L c)))
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuantumDetOppositeNegStatement
section
open Formalism.REAL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quantum_det_opposite_neg : ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (X : Fin n → Fin n → A), Formalism.REAL.GlRel X → ∀ v : ℂ, MulOpposite.unop (Formalism.REAL.qdet (fun i j => MulOpposite.op (-X i j)) v) = ((-1 : ℂ) ^ n) • Formalism.REAL.qdet X ((n : ℂ) - 1 - v) := by
  first | exact @GlobalTheory.CompanionTheory.CapelliAntipode.unop_qdet_op_neg | exact GlobalTheory.CompanionTheory.CapelliAntipode.unop_qdet_op_neg | (intros; apply GlobalTheory.CompanionTheory.CapelliAntipode.unop_qdet_op_neg <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelIndexAnnihilatorsDualityStatement
section
open Matrix
open scoped Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relIndex_annihilators_duality : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ψ ≠ 1 → ∀ (n : ℕ) (A₀ A P₀ P : AddSubgroup (Fin n → k)), IsCompact (A₀ : Set (Fin n → k)) → IsOpen (A₀ : Set (Fin n → k)) → IsCompact (A : Set (Fin n → k)) → IsOpen (A : Set (Fin n → k)) → A₀ ≤ A → (∀ ξ, ξ ∈ P₀ ↔ ∀ a ∈ A₀, ψ (ξ ⬝ᵥ a) = 1) → (∀ ξ, ξ ∈ P ↔ ∀ a ∈ A, ψ (ξ ⬝ᵥ a) = 1) → P.relIndex P₀ = A₀.relIndex A := by
  first | exact @GlobalTheory.CompanionTheory.IndexDuality.relIndex_annihilator_eq | exact GlobalTheory.CompanionTheory.IndexDuality.relIndex_annihilator_eq | (intros; apply GlobalTheory.CompanionTheory.IndexDuality.relIndex_annihilator_eq <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RelIndexLatticeEqHaarDet
section
open MeasureTheory Matrix
open scoped ENNReal

namespace GlobalTheory.CompanionTheory.IndexDet

theorem relIndex_mul_measure_of_isCompact {G : Type*} [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G)
    [μ.IsAddLeftInvariant] {H L : AddSubgroup G} (hL : IsCompact (L : Set G))
    (hH : IsOpen (H : Set G)) (hHL : H ≤ L) :
    (H.relIndex L : ℝ≥0∞) * μ H = μ L := by
  haveI : CompactSpace L := isCompact_iff_compactSpace.mp hL
  have ho : IsOpen ((H.addSubgroupOf L : AddSubgroup L) : Set L) := hH.preimage continuous_subtype_val
  haveI : Finite (L ⧸ H.addSubgroupOf L) := AddSubgroup.quotient_finite_of_isOpen _ ho
  haveI : (H.addSubgroupOf L).FiniteIndex := AddSubgroup.finiteIndex_of_finite_quotient
  exact GlobalTheory.BaseModule.addRelIndex_mul_measure H L hHL hH.measurableSet μ

theorem relIndex_eq_distribHaarChar_det_mul (k : Type) [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (g : GL (Fin n) k)
    (A₀ A : AddSubgroup (Fin n → k)) (hA : IsCompact (A : Set (Fin n → k)))
    (hA₀ : IsOpen (A₀ : Set (Fin n → k))) (h₀ : A₀ ≤ A)
    (h₁ : A₀ ≤ A.comap (Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) k)).toAddMonoidHom) :
    ((A₀.relIndex A : ℕ) : ℝ) = (distribHaarChar k (Matrix.GeneralLinearGroup.det g) : ℝ) *
      ((A₀.relIndex (A.comap (Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) k)).toAddMonoidHom) : ℕ) : ℝ) := by
  borelize k
  haveI := GlobalTheory.SplitWeil.secondCountable k
  haveI := GlobalTheory.SplitWeil.t2Space k
  set B := A.comap (Matrix.mulVecLin (g : Matrix (Fin n) (Fin n) k)).toAddMonoidHom with hB
  let μ : Measure (Fin n → k) := Measure.pi fun _ : Fin n => (Measure.addHaar : Measure k)
  have hBset : (B : Set (Fin n → k)) = (fun x => (g⁻¹).val *ᵥ x) '' (A : Set (Fin n → k)) := by
    ext x
    constructor
    · intro hx
      refine ⟨g.val *ᵥ x, hx, ?_⟩
      simp only [mulVec_mulVec, Units.inv_mul, one_mulVec]
    · rintro ⟨y, hy, rfl⟩
      change g.val *ᵥ ((g⁻¹).val *ᵥ y) ∈ A
      simpa only [mulVec_mulVec, Units.mul_inv, one_mulVec, SetLike.mem_coe] using hy
  have hBc : IsCompact (B : Set (Fin n → k)) := by
    rw [hBset]
    exact hA.image (by fun_prop)
  have hAm : MeasurableSet (A : Set (Fin n → k)) := hA.measurableSet
  have hm : Measurable (g.val.mulVec) := (continuous_const.matrix_mulVec continuous_id).measurable
  have hscale : μ A = (distribHaarChar k (Matrix.GeneralLinearGroup.det g) : ℝ≥0∞) * μ B := by
    have h := GlobalTheory.WeilM.smul_map_mulVec_pi (Measure.addHaar : Measure k) g.val
      (Matrix.GeneralLinearGroup.det g) rfl
    have h2 := congrArg (fun m : Measure (Fin n → k) => m (A : Set (Fin n → k))) h
    simp only [Measure.smul_apply, smul_eq_mul, Measure.map_apply hm hAm] at h2
    exact h2.symm
  have i1 := relIndex_mul_measure_of_isCompact μ hA hA₀ h₀
  have i2 := relIndex_mul_measure_of_isCompact μ hBc hA₀ h₁
  have hpos : μ A₀ ≠ 0 := (hA₀.measure_pos μ ⟨0, A₀.zero_mem⟩).ne'
  have htop : μ A₀ ≠ ∞ := ((measure_mono h₀).trans_lt hA.measure_lt_top).ne
  have key : ((A₀.relIndex A : ℕ) : ℝ≥0∞) =
      (distribHaarChar k (Matrix.GeneralLinearGroup.det g) : ℝ≥0∞) * ((A₀.relIndex B : ℕ) : ℝ≥0∞) := by
    refine (ENNReal.mul_left_inj hpos htop).mp ?_
    rw [i1, hscale, ← i2, mul_assoc]
  have := congrArg ENNReal.toReal key
  simpa using this

end GlobalTheory.CompanionTheory.IndexDet
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SamePartitionStatementStatement
section
open ReciprocityTheory.Ty.Fin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.same_partition_statement : ReciprocityTheory.Ty.Fin.St.SamePart := by
  first | exact @GlobalTheory.CompanionTheory.TyFinSamePart.samePart | exact GlobalTheory.CompanionTheory.TyFinSamePart.samePart | (intros; apply GlobalTheory.CompanionTheory.TyFinSamePart.samePart <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ScalingMeasureProductArchimedeanStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.Equi
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scaling_measure_product_archimedean : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ θ : ℝ →+* Ainf F, Continuous θ → ∀ li : Measure (Ainf F), li.IsAddHaarMeasure → ∀ (ι : Type) [Fintype ι] (ε : ℝ), 0 < ε → Measure.map (fun (y : ι → Ainf F) (i : ι) => θ ε * y i) (Measure.pi fun _ => li) = ENNReal.ofReal ((ε ^ (Module.finrank ℚ F * Fintype.card ι))⁻¹) • Measure.pi fun _ => li := by
  first | exact @GlobalTheory.CompanionTheory.Equi.InfScale.map_theta_mul_pi | exact GlobalTheory.CompanionTheory.Equi.InfScale.map_theta_mul_pi | (intros; apply GlobalTheory.CompanionTheory.Equi.InfScale.map_theta_mul_pi <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SimpleIffIrreducibleStatement
section
open ReciprocityTheory.Ty.Fin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.simple_iff_irreducible : ReciprocityTheory.Ty.Fin.St.SimpleIffIrr := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.simpleIffIrr | exact GlobalTheory.CompanionTheory.TyFin.simpleIffIrr | (intros; apply GlobalTheory.CompanionTheory.TyFin.simpleIffIrr <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TailSumOverPlacesSmallStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.Mass.MeanV PositivityTheory.Rg.Mass NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped ENNReal NNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tail_sum_over_places_small : ∀ (F : Type) [Field F] [NumberField F] (C : ℝ), 0 ≤ C → ∀ η : ℝ, 0 < η → ∃ T₀ : Finset (HeightOneSpectrum (𝓞 F)), ∀ T, T₀ ⊆ T → ∀ U : Finset (HeightOneSpectrum (𝓞 F)), ∑ D ∈ U.powerset with ¬ D ⊆ T, ∏ v ∈ D, (2 * C / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) ≤ η := by
  first | exact @GlobalTheory.CompanionTheory.Mass.MeanV.tail_sum_finset_prod_two_mul_div_sq | exact GlobalTheory.CompanionTheory.Mass.MeanV.tail_sum_finset_prod_two_mul_div_sq | (intros; apply GlobalTheory.CompanionTheory.Mass.MeanV.tail_sum_finset_prod_two_mul_div_sq <;> assumption)
end

