import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.ContinuousTorusCharacter
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0005
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0013
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0003
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0004
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0014
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0002
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0015
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0007

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HeckePairTop
section
noncomputable section

open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi

namespace UpperTheory.V.AlgebraTools

section Gen

variable {A G M : Type} [CommRing A] [Group G] [AddCommGroup M] [Module A M]

def FinOrb (K K' : Subgroup G) (x : G) : Prop := (MulAction.orbit K (x : G ⧸ K')).Finite

def HeckePair (I : Subgroup G) : Prop := ∀ x : G, FinOrb I I x

theorem heckePair_top : HeckePair (⊤ : Subgroup G) := fun _ =>
  have : Subsingleton (G ⧸ (⊤ : Subgroup G)) := QuotientGroup.subsingleton_quotient_top
  Set.toFinite _

open Classical in

def hk2 (ρ : Representation A G M) (K K' : Subgroup G) (x : G) : fixd ρ K' →ₗ[A] fixd ρ K :=
  if h : ∀ v ∈ fixd ρ K', dc ρ K K' x v ∈ fixd ρ K then (dc ρ K K' x).restrict h else 0

def hk (ρ : Representation A G M) (I : Subgroup G) (x : G) : Module.End A (fixd ρ I) := hk2 ρ I I x

theorem fixd_anti (ρ : Representation A G M) {I K : Subgroup G} (h : I ≤ K) : fixd ρ K ≤ fixd ρ I :=
  fun _ hv u hu => hv u (h hu)

def inc (ρ : Representation A G M) {I K : Subgroup G} (h : I ≤ K) : fixd ρ K →ₗ[A] fixd ρ I :=
  Submodule.inclusion (fixd_anti ρ h)

def trc (ρ : Representation A G M) (K I : Subgroup G) : fixd ρ I →ₗ[A] fixd ρ K := hk2 ρ K I 1

variable (A) in

abbrev permRep (I : Subgroup G) : Representation A G (MonoidAlgebra A (G ⧸ I)) := Representation.ofMulAction A G (G ⧸ I)

variable (A) in

def HkAlg (I : Subgroup G) : Subalgebra A (Module.End A (fixd (permRep A I) I)) :=
  Algebra.adjoin A (Set.range (hk (permRep A I) I))

variable (A) in

def hT (I : Subgroup G) (x : G) : HkAlg A I := ⟨hk (permRep A I) I x, Algebra.subset_adjoin ⟨x, rfl⟩⟩

structure LeviFact (I : Subgroup G) where
  Uf : Subgroup G
  Mf : Subgroup G
  Lf : Subgroup G
  M_U : ∀ m ∈ Mf, ∀ u ∈ Uf, m * u * m⁻¹ ∈ Uf
  M_L : ∀ m ∈ Mf, ∀ l ∈ Lf, m * l * m⁻¹ ∈ Lf
  uniq : ∀ u ∈ Uf, ∀ m ∈ Mf, ∀ l ∈ Lf, u * m * l = 1 → u = 1 ∧ m = 1
  fact : ∀ g ∈ I, ∃ u ∈ Uf ⊓ I, ∃ m ∈ Mf ⊓ I, ∃ l ∈ Lf ⊓ I, g = u * m * l

def LeviFact.triv (I : Subgroup G) : LeviFact I where
  Uf := ⊥
  Mf := ⊤
  Lf := ⊥
  M_U m _ u hu := by simpa using hu
  M_L m _ u hu := by simpa using hu
  uniq u hu m _ l hl h := by
    have h1 : u = 1 := by simpa using hu
    have h2 : l = 1 := by simpa using hl
    simpa [h1, h2] using h
  fact g hg := ⟨1, one_mem _, g, ⟨trivial, hg⟩, 1, one_mem _, by simp⟩

def LeviFact.Pos {I : Subgroup G} (F : LeviFact I) (m : G) : Prop :=
  m ∈ F.Mf ∧ (∀ u ∈ F.Uf ⊓ I, m * u * m⁻¹ ∈ I) ∧ ∀ l ∈ F.Lf ⊓ I, m⁻¹ * l * m ∈ I

def LeviFact.NormJ {I : Subgroup G} (F : LeviFact I) (m : G) : Prop :=
  ∀ j ∈ F.Mf ⊓ I, m * j * m⁻¹ ∈ I ∧ m⁻¹ * j * m ∈ I

end Gen

section Perm

variable {n : ℕ}

def invLen (w : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ w p.2 < w p.1).card

def pm (R : Type) [CommRing R] (n : ℕ) : Equiv.Perm (Fin n) →* GL (Fin n) R :=
  (Matrix.permMatrixHom (n := Fin n) (R := R)).toHomUnits

theorem pm_apply (R : Type) [CommRing R] (w : Equiv.Perm (Fin n)) (i j : Fin n) :
    (pm R n w : Matrix (Fin n) (Fin n) R) i j = if i = w j then 1 else 0 := by
  simp only [pm, MonoidHom.coe_toHomUnits, Matrix.permMatrixHom_apply, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Option.mem_def, Option.some.injEq]
  congr 1
  exact propext Equiv.Perm.inv_eq_iff_eq

end Perm

section GeneralLinearIntegers

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ)

def unitsC (C : Subgroup 𝓀[k]ˣ) : Subgroup kˣ :=
  (C.comap (Units.map (IsLocalRing.residue 𝒪[k]).toMonoidHom)).map (Units.map (algebraMap 𝒪[k] k).toMonoidHom)

def torC (C : Subgroup 𝓀[k]ˣ) : Subgroup (Fin n → kˣ) := Subgroup.pi Set.univ fun _ => unitsC k C

def unipO : Subgroup (GL (Fin n) k) := unipB k (Fin n) ⊓ KO k (Fin n)

def iwC (C : Subgroup 𝓀[k]ˣ) : Subgroup (GL (Fin n) k) :=
  KOne k (Fin n) ⊔ unipO k n ⊔ (torC k n C).map (diagT k (Fin n))

variable {k n}

def IsUnif (x : kˣ) : Prop := ∃ p : 𝒪[k], Irreducible p ∧ algebraMap 𝒪[k] k p = x

def Dom (t : Fin n → kˣ) : Prop := ∀ i j, i ≤ j → valuation k (t i : k) ≤ valuation k (t j : k)

theorem dom_one : Dom (1 : Fin n → kˣ) := fun _ _ _ => le_rfl

def pw (x : kˣ) (a : Fin n → ℤ) : GL (Fin n) k := diagT k (Fin n) fun i => x ^ a i

def fund (n m : ℕ) : Fin n → ℤ := fun i => if (i : ℕ) < m then 1 else 0

theorem exists_isUnif : ∃ x : kˣ, IsUnif x := by
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[k]
  have : algebraMap 𝒪[k] k p ≠ 0 := fun h => hp.ne_zero (Subtype.ext h)
  exact ⟨Units.mk0 _ this, p, hp, rfl⟩

end GeneralLinearIntegers

end UpperTheory.V.AlgebraTools
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.InjOfSandwich
section
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

private theorem inj_of_sandwich {R Q F ι : Type*} [CommRing R] [AddCommGroup Q] [Module R Q]
    [AddCommGroup F] [Module R F] [Fintype ι] (g : (ι → R) →ₗ[R] Q) (f : Q →ₗ[R] F)
    (e : F ≃ₗ[R] (ι → R)) (hg : Function.Surjective g) (hf : Function.Surjective f) :
    Function.Injective f := by
  have hs : Function.Surjective (e.toLinearMap ∘ₗ f ∘ₗ g) := e.surjective.comp (hf.comp hg)
  have hi := OrzechProperty.injective_of_surjective_endomorphism _ hs
  intro a b hab
  obtain ⟨x, rfl⟩ := hg a
  obtain ⟨y, rfl⟩ := hg b
  have : x = y := hi (by simp [hab])
  rw [this]

theorem UpperTheory.V.AlgebraTools.groupRing_ker :
    ∀ (Λ : Type) [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (IsLocalRing.maximalIdeal Λ) Λ] (l : ℕ), l.Prime → (l : Λ) ∈ IsLocalRing.maximalIdeal Λ → ∀ (σ : Type) [Fintype σ] [DecidableEq σ] (e : σ → ℕ) (φ : MvPowerSeries σ Λ →ₐ[Λ] MonoidAlgebra Λ (∀ s, Multiplicative (ZMod (l ^ e s)))), (∀ s : σ, φ (1 + MvPowerSeries.X s) = MonoidAlgebra.of Λ (∀ s, Multiplicative (ZMod (l ^ e s))) (Pi.mulSingle s (Multiplicative.ofAdd (1 : ZMod (l ^ e s))))) → Function.Surjective φ →
      RingHom.ker φ = Ideal.span (Set.range fun s => (1 + MvPowerSeries.X s : MvPowerSeries σ Λ) ^ l ^ e s - 1) := by
  intro Λ _ _ _ _ l hl hlm σ _ _ e φ hφ hsurj
  haveI : ∀ s, NeZero (l ^ e s) := fun s => ⟨pow_ne_zero _ hl.ne_zero⟩
  set w : σ → MvPowerSeries σ Λ := fun s => (1 + MvPowerSeries.X s) ^ l ^ e s - 1 with hw
  set I : Ideal (MvPowerSeries σ Λ) := Ideal.span (Set.range w) with hI
  have hle : I ≤ RingHom.ker φ := by
    rw [hI, Ideal.span_le]
    rintro _ ⟨s, rfl⟩
    have h1 : (Pi.mulSingle s (Multiplicative.ofAdd (1 : ZMod (l ^ e s))) :
        ∀ s, Multiplicative (ZMod (l ^ e s))) ^ (l ^ e s) = 1 := by
      rw [← Pi.mulSingle_pow, ← ofAdd_nsmul, nsmul_one, ZMod.natCast_self, ofAdd_zero,
        Pi.mulSingle_one]
    simp only [SetLike.mem_coe, RingHom.mem_ker, hw, map_sub, map_pow, hφ, map_one]
    rw [← map_pow, h1, map_one, sub_self]
  have hwm : ∀ s, w s - MvPowerSeries.X s ^ (l ^ e s) ∈
      Ideal.map MvPowerSeries.C (IsLocalRing.maximalIdeal Λ) := by
    intro s
    obtain ⟨m, hm⟩ : ∃ m, l ^ e s = m + 1 := ⟨l ^ e s - 1, (Nat.succ_pred_eq_of_pos (pow_pos hl.pos _)).symm⟩
    have hlC : ((l : ℕ) : MvPowerSeries σ Λ) ∈ Ideal.map MvPowerSeries.C (IsLocalRing.maximalIdeal Λ) := by
      rw [← map_natCast (MvPowerSeries.C (σ := σ) (R := Λ))]
      exact Ideal.mem_map_of_mem _ hlm
    simp only [hw]
    rw [add_comm, add_pow, hm, Finset.sum_range_succ, Finset.sum_range_succ']
    have key : ∀ k ∈ Finset.range m, MvPowerSeries.X s ^ (k + 1) * (1 : MvPowerSeries σ Λ) ^ (m + 1 - (k + 1)) *
        (((m + 1).choose (k + 1) : ℕ) : MvPowerSeries σ Λ) ∈ Ideal.map MvPowerSeries.C (IsLocalRing.maximalIdeal Λ) := by
      intro k hk
      have hd : l ∣ (m + 1).choose (k + 1) := by
        rw [← hm]
        refine hl.dvd_choose_pow (Nat.succ_ne_zero k) ?_
        rw [hm]; have := Finset.mem_range.mp hk; omega
      obtain ⟨t, ht⟩ := hd
      rw [ht, Nat.cast_mul]
      exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ hlC)
    have hsum := Ideal.sum_mem _ key
    simp only [pow_zero, one_pow, mul_one, Nat.choose_zero_right, Nat.choose_self, Nat.cast_one,
      Nat.sub_zero, one_mul] at hsum ⊢
    convert hsum using 1
    ring
  have hIφ : ∀ a ∈ I, φ a = 0 := fun a ha => hle ha
  refine le_antisymm ?_ hle
  have hspan := UpperTheory.V.AlgebraTools.mvPowerSeries_span_monomials Λ σ (fun s => l ^ e s) w hwm
  let ψ := Ideal.Quotient.liftₐ I φ hIφ
  have hψs : Function.Surjective ψ := by
    intro y
    obtain ⟨x, rfl⟩ := hsurj y
    exact ⟨Ideal.Quotient.mk I x, rfl⟩
  let v := fun α : ((s : σ) → Fin (l ^ e s)) => Ideal.Quotient.mk I (∏ s, MvPowerSeries.X s ^ (α s : ℕ))
  have hg : Function.Surjective (Fintype.linearCombination Λ v) := by
    rw [← LinearMap.range_eq_top, Fintype.range_linearCombination]
    exact hspan
  let eqv : ((s : σ) → Fin (l ^ e s)) ≃ (∀ s, Multiplicative (ZMod (l ^ e s))) :=
    Equiv.piCongrRight fun s => (ZMod.finEquiv (l ^ e s)).toEquiv.trans Multiplicative.ofAdd
  let E : MonoidAlgebra Λ (∀ s, Multiplicative (ZMod (l ^ e s))) ≃ₗ[Λ] (((s : σ) → Fin (l ^ e s)) → Λ) :=
    (MonoidAlgebra.coeffLinearEquiv Λ).trans
      ((Finsupp.linearEquivFunOnFinite Λ Λ _).trans (LinearEquiv.funCongrLeft Λ Λ eqv))
  have hinj := inj_of_sandwich (Fintype.linearCombination Λ v) ψ.toLinearMap E hg hψs
  intro x hx
  have h0 : ψ (Ideal.Quotient.mk I x) = 0 := hx
  have : Ideal.Quotient.mk I x = 0 := hinj (by simpa using h0)
  exact Ideal.Quotient.eq_zero_iff_mem.mp this
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.LemmaL
section
open Polynomial Matrix IsLocalRing TensorProduct UpperTheory.V.AlgebraTools

private theorem UpperTheory.V.AlgebraTools.entry_of_single {R ι : Type} [CommRing R] [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι R) (a b : ι) :
    (single a a (1 : R) * M * single b b (1 : R) : Matrix ι ι R) a b = M a b := by
  simp

theorem UpperTheory.V.AlgebraTools.lemma_L :
    ∀ {R Γ : Type} [CommRing R] [IsLocalRing R] [Group Γ] {n : ℕ} (r : Γ →* GL (Fin n) R) (ψ : Fin n → Γ →* Rˣ), (n : Cardinal) ≤ Cardinal.mk (ResidueField R) → (∀ g : Fin n → Γ, (List.ofFn fun i => ((r (g i) : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) - algebraMap R _ ((ψ i (g i) : Rˣ) : R)).prod = 0) → Function.Injective (fun i => (residue R : R →* ResidueField R).comp ((Units.coeHom R).comp (ψ i))) → (∀ z : MonoidAlgebra R Γ, (MonoidAlgebra.lift R (Matrix (Fin n) (Fin n) R) Γ ((Units.coeHom _).comp r) z).charpoly.map (residue R) = ∏ i, (X - C (residue R (MonoidAlgebra.lift R R Γ ((Units.coeHom _).comp (ψ i)) z)))) → ∃ (z : MonoidAlgebra R Γ) (g : GL (Fin n) R), (∀ i j, i ≠ j → IsUnit (MonoidAlgebra.lift R R Γ ((Units.coeHom R).comp (ψ i)) z - MonoidAlgebra.lift R R Γ ((Units.coeHom R).comp (ψ j)) z)) ∧ (∀ i, (g : Matrix (Fin n) (Fin n) R) * lag (fun i => MonoidAlgebra.lift R R Γ ((Units.coeHom R).comp (ψ i)) z) (MonoidAlgebra.lift R (Matrix (Fin n) (Fin n) R) Γ ((Units.coeHom _).comp r) z) i * ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = single i i 1) ∧ ∀ s, (∀ i j, j < i → (g * r s * g⁻¹ : GL (Fin n) R) i j = 0) ∧ ∀ i, (g * r s * g⁻¹ : GL (Fin n) R) i i = (ψ i s : R) := by
  intro R Γ _ _ _ n r ψ hcard hprod hinj hchar
  obtain ⟨z, hz⟩ := sep_chars (fun i => (Units.coeHom R).comp (ψ i)) hcard hinj
  have hord := ord_ext ((Units.coeHom _).comp r) (fun i => (Units.coeHom R).comp (ψ i)) hprod
  obtain ⟨hcoi, htri, hdiag⟩ := lag_triangular
    (MonoidAlgebra.lift R (Matrix (Fin n) (Fin n) R) Γ ((Units.coeHom _).comp r))
    (fun i => MonoidAlgebra.lift R R Γ ((Units.coeHom R).comp (ψ i))) z hord hz
  have hne := lag_ne_zero (fun i => MonoidAlgebra.lift R R Γ ((Units.coeHom R).comp (ψ i)) z) _ hz (hchar z)
  obtain ⟨g, hg⟩ := coi_conj_single _ hcoi hne
  refine ⟨z, g, hz, hg, fun s => ?_⟩
  set e := lag (fun i => MonoidAlgebra.lift R R Γ ((Units.coeHom R).comp (ψ i)) z)
    (MonoidAlgebra.lift R (Matrix (Fin n) (Fin n) R) Γ ((Units.coeHom _).comp r) z) with he
  have hρ : MonoidAlgebra.lift R (Matrix (Fin n) (Fin n) R) Γ ((Units.coeHom _).comp r)
      (MonoidAlgebra.of R Γ s) = ((r s : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) := by
    simp [MonoidAlgebra.lift_of]
  have hχ : ∀ i, MonoidAlgebra.lift R R Γ ((Units.coeHom R).comp (ψ i)) (MonoidAlgebra.of R Γ s)
      = ((ψ i s : Rˣ) : R) := fun i => by
    simp [MonoidAlgebra.lift_of]
  have hinv : ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) * (g : Matrix (Fin n) (Fin n) R) = 1 :=
    Units.inv_mul g
  have key : ∀ i j, ((g * r s * g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) i j =
      ((g : Matrix (Fin n) (Fin n) R) * (e i * ((r s : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) * e j)
        * ((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)) i j := by
    intro i j
    refine (UpperTheory.V.AlgebraTools.entry_of_single (((g * r s * g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)) i j).symm.trans ?_
    rw [← hg i, ← hg j]
    congr 1
    simp only [Units.val_mul, Matrix.mul_assoc]
    simp only [← Matrix.mul_assoc (((g⁻¹ : GL (Fin n) R) : Matrix (Fin n) (Fin n) R)), hinv, Matrix.one_mul]
  refine ⟨fun i j hji => ?_, fun i => ?_⟩
  · rw [key, ← hρ, htri _ i j hji]
    simp
  · rw [key, ← hρ, hdiag, Matrix.mul_smul, Matrix.smul_mul, hg i, hχ]
    simp
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.MSpBasis
section
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

theorem UpperTheory.V.AlgebraTools.mSplitAlg_basis :
    ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (n : ℕ) (R : Type) [CommRing R] (P : κ → Polynomial R), (∀ j, (P j).Monic) → (∀ j, (P j).natDegree = n) →
      ∃ b : Module.Basis (κ → ∀ i : Fin n, Fin (n - i)) R (MSplitAlg P n), ∀ c, b c = ∏ j, ∏ i, MSplitAlg.root P n j i ^ (c j i : ℕ) := by
  intro κ _ _ n R _ P hm hd
  have hb := fun j => (UpperTheory.V.AlgebraTools.splitAlg_basis n R (P j) (hm j) (hd j)).1
  choose bj hbj using hb
  let f : ∀ j, SplitAlg (P j) n →ₐ[R] MSplitAlg P n := fun j =>
    SplitAlg.lift (P j) n (MSplitAlg.root P n j) (MSplitAlg.prod_root P n j)
  let M : MultilinearMap R (fun j => SplitAlg (P j) n) (MSplitAlg P n) :=
    (MultilinearMap.mkPiAlgebra R κ (MSplitAlg P n)).compLinearMap (fun j => (f j).toLinearMap)
  have hM : ∀ x, M x = ∏ j, f j (x j) := fun x => by
    simp [M, MultilinearMap.compLinearMap_apply, MultilinearMap.mkPiAlgebra_apply]
  let ψ : (⨂[R] j, SplitAlg (P j) n) →ₐ[R] MSplitAlg P n :=
    PiTensorProduct.liftAlgHom M (by rw [hM]; simp)
      (fun x y => by rw [hM, hM, hM]; simp [Finset.prod_mul_distrib])
  have hψt : ∀ x, ψ (PiTensorProduct.tprod R x) = ∏ j, f j (x j) := fun x => by
    simp [ψ, hM]
  have hψs : ∀ j x, ψ (PiTensorProduct.singleAlgHom j x) = f j x := fun j x => by
    rw [PiTensorProduct.singleAlgHom_apply, hψt,
      Fintype.prod_eq_single j (fun k hk => by simp [Pi.mulSingle_eq_of_ne hk])]
    simp
  let φ : MSplitAlg P n →ₐ[R] (⨂[R] j, SplitAlg (P j) n) :=
    MSplitAlg.lift P n (fun j i => PiTensorProduct.singleAlgHom j (SplitAlg.root (P j) n i)) (fun j => by
      have := congrArg (Polynomial.map
        (PiTensorProduct.singleAlgHom (R := R) (A := fun j => SplitAlg (P j) n) j).toRingHom)
        (SplitAlg.prod_root (P j) n)
      simp only [Polynomial.map_prod, Polynomial.map_map, AlgHom.toRingHom_eq_coe, AlgHom.comp_algebraMap,
        Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, RingHom.coe_coe] at this
      exact this)
  have h1 : ψ.comp φ = AlgHom.id R (MSplitAlg P n) := MSplitAlg.hom_ext P n (fun j i => by
    simp only [AlgHom.comp_apply, AlgHom.id_apply, φ, MSplitAlg.lift_root, hψs, f, SplitAlg.lift_root])
  have h2 : φ.comp ψ = AlgHom.id R _ := PiTensorProduct.algHom_ext (fun j => SplitAlg.hom_ext (P j) n (fun i => by
    simp only [AlgHom.comp_apply, AlgHom.id_apply, hψs, f, SplitAlg.lift_root, φ, MSplitAlg.lift_root]))
  let e : MSplitAlg P n ≃ₐ[R] (⨂[R] j, SplitAlg (P j) n) := AlgEquiv.ofAlgHom φ ψ h2 h1
  refine ⟨(Basis.piTensorProduct bj).map e.symm.toLinearEquiv, fun c => ?_⟩
  rw [Module.Basis.map_apply, Basis.piTensorProduct_apply]
  show ψ _ = _
  rw [hψt]
  refine Finset.prod_congr rfl (fun j _ => ?_)
  rw [hbj j (c j), map_prod]
  simp only [map_pow, f, SplitAlg.lift_root]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.SwapOneAlt
section
open MvPolynomial Equiv UpperTheory.V.AlgebraTools.Hk

private theorem pair_lt {R : Type} [CommRing R] {n : ℕ} {q : R} {H : Type} [Ring H] [Algebra R H] (b : Bern n q H)
    {a c : Fin n} (h : a.val + 1 = c.val) (u : Perm (Fin n)) (hu : u⁻¹ a < u⁻¹ c) :
    (b.T (swap a c) * b.T u - q • b.T u) + (b.T (swap a c) * b.T (swap a c * u) - q • b.T (swap a c * u)) = 0 := by
  have hu : b.T (swap a c * u) = b.T (swap a c) * b.T u := b.T_mul a c h u hu
  have hsq := b.T_sq a c h
  rw [hu, ← mul_assoc, hsq, add_mul, smul_mul_assoc, smul_mul_assoc, one_mul]
  module

private theorem swap_one {R : Type} [CommRing R] {n : ℕ} {q : R} {H : Type} [Ring H] [Algebra R H] (b : Bern n q H)
    {a c : Fin n} (h : a.val + 1 = c.val) : b.T (swap a c) * b.one = q • b.one := by
  have hac : a ≠ c := by
    intro e
    rw [e] at h
    omega
  have key : ∀ w : Perm (Fin n), (b.T (swap a c) * b.T w - q • b.T w)
      + (b.T (swap a c) * b.T (swap a c * w) - q • b.T (swap a c * w)) = 0 := by
    intro w
    rcases lt_or_gt_of_ne (show w⁻¹ a ≠ w⁻¹ c from fun e => hac (w⁻¹.injective e)) with hw | hw
    · exact pair_lt b h w hw
    · have hu : (swap a c * w)⁻¹ a < (swap a c * w)⁻¹ c := by
        simpa [Perm.mul_apply, mul_inv_rev, swap_inv, swap_apply_left, swap_apply_right] using hw
      have := pair_lt b h (swap a c * w) hu
      rw [← mul_assoc, swap_mul_self, one_mul] at this
      rw [add_comm]
      exact this
  have hsum : ∑ w, (b.T (swap a c) * b.T w - q • b.T w) = 0 := by
    refine Finset.sum_ninvolution (fun w => swap a c * w) key ?_ (fun _ => Finset.mem_univ _) ?_
    · intro w _ e
      apply hac
      have := congrArg (fun x : Perm (Fin n) => (x * w⁻¹) a) e
      simp [mul_assoc] at this
      exact this.symm
    · intro w
      rw [← mul_assoc, swap_mul_self, one_mul]
  unfold Bern.one
  rw [Finset.mul_sum, Finset.smul_sum, ← sub_eq_zero, ← Finset.sum_sub_distrib]
  exact hsum

theorem UpperTheory.V.AlgebraTools.hkOne :
    ∀ (R : Type) [CommRing R] (n : ℕ) (q : R) (H : Type) [Ring H] [Algebra R H] (b : Bern n q H),
      (∀ w, b.T w * b.one = q ^ invN w • b.one) ∧ b.one * b.one = poin n q • b.one := by
  intro R _ n q H _ _ b
  have hinv := UpperTheory.V.AlgebraTools.hkInv n
  have p1 : ∀ w, b.T w * b.one = q ^ invN w • b.one := by
    refine UpperTheory.V.AlgebraTools.hkInd n _ ?_ ?_
    · rw [b.T_one, one_mul]
      simp [invN, hinv.2.2.1]
    · intro a c h w hw ih
      rw [b.T_mul a c h w hw, mul_assoc, ih, mul_smul_comm, swap_one b h, smul_smul,
        (hinv.1 a c h w hw).2.2, pow_succ]
  refine ⟨p1, ?_⟩
  show (∑ w, b.T w) * b.one = _
  rw [Finset.sum_mul]
  simp_rw [p1]
  rw [← Finset.sum_smul]
  rfl
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.TnFree
section
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

theorem UpperTheory.V.AlgebraTools.topNil_free :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R] (κ : Type) (M : Type) [AddCommGroup M] [Module R M] [Module.Finite R M] (T : κ → Module.End R M), (∀ i j, Commute (T i) (T j)) →
      (∃ C : Submodule R M, IsCompl (topNil (IsLocalRing.maximalIdeal R) T) C ∧ ∀ φ : Module.End R M, (∀ i, Commute φ (T i)) →
        (∀ x ∈ topNil (IsLocalRing.maximalIdeal R) T, φ x ∈ topNil (IsLocalRing.maximalIdeal R) T) ∧ ∀ x ∈ C, φ x ∈ C) ∧
      (∀ I : Ideal R, (I • ⊤ : Submodule R M) ⊓ topNil (IsLocalRing.maximalIdeal R) T = I • topNil (IsLocalRing.maximalIdeal R) T) ∧
      (∀ i, ∃ r : ℕ, ∀ x ∈ topNil (IsLocalRing.maximalIdeal R) T, (T i ^ r) x ∈ (IsLocalRing.maximalIdeal R) • topNil (IsLocalRing.maximalIdeal R) T) ∧
      (Module.Free R M → Module.Free R (topNil (IsLocalRing.maximalIdeal R) T) ∧ Module.finrank R (topNil (IsLocalRing.maximalIdeal R) T) ≤ Module.finrank R M) := by
  intro R _ _ _ _ κ M _ _ _ T hT
  obtain ⟨e, he, hid, hr⟩ := UpperTheory.V.AlgebraTools.exists_idem_topNil R κ M T hT
  have hee : ∀ x, e (e x) = e x := fun x => by
    have h := congrArg (fun f : Module.End R M => f x) hid.eq
    simpa using h
  have hfix : ∀ x ∈ topNil (IsLocalRing.maximalIdeal R) T, e x = x := by
    rw [← hr]
    rintro _ ⟨y, rfl⟩
    exact hee y
  have hmem : ∀ x, e x ∈ topNil (IsLocalRing.maximalIdeal R) T := fun x => by
    rw [← hr]; exact ⟨x, rfl⟩
  have hcomm : ∀ φ : Module.End R M, (∀ i, Commute φ (T i)) → ∀ x, φ (e x) = e (φ x) := by
    intro φ hφ x
    have h : Commute φ e := by
      refine Algebra.commute_of_mem_adjoin_of_forall_mem_commute he ?_
      rintro _ ⟨i, rfl⟩
      exact hφ i
    have h2 := congrArg (fun f : Module.End R M => f x) h.eq
    simpa using h2
  have hstab : ∀ φ : Module.End R M, (∀ i, Commute φ (T i)) →
      ∀ x ∈ topNil (IsLocalRing.maximalIdeal R) T, φ x ∈ topNil (IsLocalRing.maximalIdeal R) T := by
    intro φ hφ x hx
    rw [← hfix x hx, hcomm φ hφ]
    exact hmem _
  have hI : ∀ I : Ideal R, (I • ⊤ : Submodule R M) ⊓ topNil (IsLocalRing.maximalIdeal R) T =
      I • topNil (IsLocalRing.maximalIdeal R) T := by
    intro I
    refine le_antisymm ?_ (le_inf (Submodule.smul_mono le_rfl le_top) Submodule.smul_le_right)
    rintro x ⟨hx1, hx2⟩
    have h1 : e x ∈ Submodule.map e (I • ⊤ : Submodule R M) := ⟨x, hx1, rfl⟩
    rw [Submodule.map_smul'', Submodule.map_top, hr, hfix x hx2] at h1
    exact h1
  refine ⟨⟨LinearMap.ker e, ?_, fun φ hφ => ⟨hstab φ hφ, ?_⟩⟩, hI, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · rw [Submodule.disjoint_def]
      intro x hx hk
      rw [← hfix x hx]
      exact hk
    · rw [codisjoint_iff, eq_top_iff]
      intro x _
      refine Submodule.mem_sup.2 ⟨e x, hmem x, x - e x, ?_, by abel⟩
      rw [LinearMap.mem_ker, map_sub, hee, sub_self]
  · intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    rw [← hcomm φ hφ, hx, map_zero]
  · intro i
    obtain ⟨S, hS⟩ := IsNoetherian.noetherian (topNil (IsLocalRing.maximalIdeal R) T)
    have hev : ∀ᶠ r : ℕ in atTop, ∀ x ∈ S,
        (T i ^ r) x ∈ ((IsLocalRing.maximalIdeal R) ^ 1 • ⊤ : Submodule R M) := by
      rw [Filter.eventually_all_finset]
      intro x hx
      have hx' : x ∈ topNil (IsLocalRing.maximalIdeal R) T := hS ▸ Submodule.subset_span hx
      exact mem_topNil.1 hx' i 1
    obtain ⟨r, hr'⟩ := hev.exists
    refine ⟨r, fun x hx => ?_⟩
    rw [← hI]
    refine ⟨?_, hstab _ (fun j => (hT i j).pow_left r) x hx⟩
    have hle : Submodule.span R (S : Set M) ≤
        Submodule.comap (T i ^ r) ((IsLocalRing.maximalIdeal R) • ⊤ : Submodule R M) := by
      rw [Submodule.span_le]
      intro y hy
      have h := hr' y hy
      rw [pow_one] at h
      exact h
    rw [hS] at hle
    exact hle hx
  · intro hF
    refine ⟨?_, Submodule.finrank_le _⟩
    have hP : Module.Projective R (topNil (IsLocalRing.maximalIdeal R) T) :=
      Module.Projective.of_split (topNil (IsLocalRing.maximalIdeal R) T).subtype
        (LinearMap.codRestrict _ e hmem) (by
          ext x
          simpa using hfix x.1 x.2)
    exact Module.free_of_flat_of_isLocalRing
end

