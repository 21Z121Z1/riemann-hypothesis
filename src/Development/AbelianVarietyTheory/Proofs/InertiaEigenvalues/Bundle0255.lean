import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeAlgebraMapOC
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateDecompositionCompletedCyclotomicIntegers
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LiftingTheory
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0041

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OcTensorCoeffBasisCoordsMemCyclotomicLevelOfPowe
section
noncomputable section

namespace GlobalTheory.Cyc.Decomp.Coord

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.Decomp TensorProduct

variable {l : ℕ} [Fact l.Prime]

theorem inC_zero (F : IntermediateField ℚ_[l] (Om l)) : (0 : PadicComplex l) ∈ inC F :=
  ⟨0, F.zero_mem, UniformSpace.Completion.coe_zero⟩

theorem inC_add {F : IntermediateField ℚ_[l] (Om l)} {x y : PadicComplex l} (hx : x ∈ inC F)
    (hy : y ∈ inC F) : x + y ∈ inC F := by
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨v, hv, rfl⟩ := hy
  exact ⟨u + v, F.add_mem hu hv, UniformSpace.Completion.coe_add _ _⟩

theorem inC_mul {F : IntermediateField ℚ_[l] (Om l)} {x y : PadicComplex l} (hx : x ∈ inC F)
    (hy : y ∈ inC F) : x * y ∈ inC F := by
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨v, hv, rfl⟩ := hy
  exact ⟨u * v, F.mul_mem hu hv, UniformSpace.Completion.coe_mul _ _⟩

theorem inC_zC (F : IntermediateField ℚ_[l] (Om l)) (x : ℤ_[l]) : zC x ∈ inC F :=
  ⟨algebraMap ℚ_[l] (Om l) (x : ℚ_[l]), F.algebraMap_mem _, rfl⟩

theorem inC_sum {F : IntermediateField ℚ_[l] (Om l)} {ι : Type} (s : Finset ι)
    (g : ι → PadicComplex l) (h : ∀ i ∈ s, g i ∈ inC F) : ∑ i ∈ s, g i ∈ inC F :=
  Finset.sum_induction g (· ∈ inC F) (fun _ _ => inC_add) (inC_zero F) h

theorem kap_sum {LL : FinExt l} {f : ℕ} (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL)) {ι : Type}
    (s : Finset ι) (g : ι → OCO LL) (k : Fin f) :
    kap o (∑ i ∈ s, g i) k = ∑ i ∈ s, kap o (g i) k := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, kap_zero]
  | insert i s hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, kap_add, ih]

theorem kap_mul_one_tmul {LL : FinExt l} {f : ℕ} (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL))
    (x : OCO LL) (a : ↥(OL LL)) (k : Fin f) :
    kap o (x * ((1 : OC l) ⊗ₜ[ℤ_[l]] a)) k = ∑ j, kap o x j * zC (o.repr (o j * a) k) := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis (OC l) o).sum_repr x]
  rw [Finset.sum_mul, kap_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', Algebra.TensorProduct.tmul_mul_tmul,
    kap_tmul, smul_eq_mul, mul_one, mul_one]
  rfl

theorem let_split {O : Type} [CommRing O] {n : ℕ} [NeZero n] (a : LetA O n) :
    ∃ a' : LetA O n, a = ∑ i, letE i * algebraMap O (LetA O n) (PowerSeries.constantCoeff (a i))
      + letπ * a' := by
  refine ⟨fun i => PowerSeries.mk fun p => PowerSeries.coeff (p + 1) (a i), funext fun j => ?_⟩
  rw [Pi.add_apply, Finset.sum_apply, Finset.sum_eq_single j]
  · simp only [letE, letπ, Pi.mul_apply, Pi.single_eq_same, one_mul, Pi.algebraMap_apply]
    rw [add_comm]
    exact PowerSeries.eq_X_mul_shift_add_const (a j)
  · intro i _ hij
    simp [letE, Pi.single_eq_of_ne hij.symm]
  · simp

theorem coord (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (m n f : ℕ) [NeZero n]
    (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL)) (φ : LetA ↥(OL LL) n →+* OCO LL) (c : OC l)
    (hO : ∀ a : ↥(OL LL), φ (algebraMap ↥(OL LL) (LetA ↥(OL LL) n) a) = (1 : OC l) ⊗ₜ[ℤ_[l]] a)
    (hπ : φ letπ = c ⊗ₜ[ℤ_[l]] (1 : ↥(OL LL))) (hc : ‖(c : PadicComplex l)‖ < 1)
    (hcF : (c : PadicComplex l) ∈ inC (Ks K m))
    (hE : ∀ i k, kap o (φ (letE i)) k ∈ inC (Ks K m)) :
    ∀ a k, kap o (φ a) k ∈ intC (Ks K m) := by
  haveI := GlobalTheory.TateDecomp.finite_Ks K m
  have hcl : IsClosed (intC (Ks K m)) := (GlobalTheory.TateDecomp.isCompact_intC (Ks K m)).isClosed
  have key : ∀ (N : ℕ) (k : Fin f) (a : LetA ↥(OL LL) n), ∃ s ∈ inC (Ks K m),
      ∃ r : PadicComplex l, ‖r‖ ≤ 1 ∧ kap o (φ a) k = s + (c : PadicComplex l) ^ N * r := by
    intro N k
    induction N with
    | zero => exact fun a => ⟨0, inC_zero _, kap o (φ a) k, norm_kap_le _ _ _, by simp⟩
    | succ N ih =>
      intro a
      obtain ⟨a', ha⟩ := let_split a
      obtain ⟨s, hs, r, hr, h⟩ := ih a'
      refine ⟨∑ i, kap o (φ (letE i) * ((1 : OC l) ⊗ₜ[ℤ_[l]] (PowerSeries.constantCoeff (a i)))) k
        + (c : PadicComplex l) * s, inC_add (inC_sum _ _ fun i _ => ?_) (inC_mul hcF hs), r, hr, ?_⟩
      · rw [kap_mul_one_tmul]
        exact inC_sum _ _ fun j _ => inC_mul (hE i j) (inC_zC _ _)
      · have e : φ a = ∑ i, φ (letE i) * ((1 : OC l) ⊗ₜ[ℤ_[l]] (PowerSeries.constantCoeff (a i)))
            + (c ⊗ₜ[ℤ_[l]] (1 : ↥(OL LL))) * φ a' := by
          refine (congrArg φ ha).trans ((φ.map_add _ _).trans ?_)
          refine congrArg₂ (· + ·) ((map_sum φ _ _).trans (Finset.sum_congr rfl fun i _ => ?_)) ?_
          · exact (φ.map_mul _ _).trans (congrArg (φ (letE i) * ·) (hO _))
          · exact (φ.map_mul _ _).trans (congrArg (· * φ a') hπ)
        rw [e, kap_add, kap_sum, kap_tmul_one_mul, h, pow_succ', mul_add, mul_assoc, add_assoc]
  intro a k
  refine hcl.closure_subset (Metric.mem_closure_iff.2 fun ε hε => ?_)
  obtain ⟨N, hN⟩ := exists_pow_lt_of_lt_one hε hc
  obtain ⟨s, hs, r, hr, h⟩ := key N k a
  have hb : ‖(c : PadicComplex l) ^ N * r‖ ≤ ‖(c : PadicComplex l)‖ ^ N := by
    rw [norm_mul, norm_pow]
    exact mul_le_of_le_one_right (by positivity) hr
  refine ⟨s, ⟨hs, ?_⟩, ?_⟩
  · have e : s = kap o (φ a) k + -((c : PadicComplex l) ^ N * r) := by rw [h]; ring
    rw [e]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (norm_kap_le _ _ _) ?_)
    rw [norm_neg]
    exact hb.trans (pow_le_one₀ (norm_nonneg _) hc.le)
  · rw [dist_eq_norm, h, add_sub_cancel_left]
    exact hb.trans_lt hN

end GlobalTheory.Cyc.Decomp.Coord
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankCount
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.Decomp TensorProduct

noncomputable section

namespace GlobalTheory.Cyc.Decomp

theorem card_eq_finrank_mul_card {Z O R T : Type} [CommRing Z] [Nontrivial Z] [CommRing O]
    [Nontrivial O] [Algebra Z O] [Module.Free Z O] [CommRing R] [Nontrivial R] [Algebra O R]
    [AddCommGroup T] [Module O T] [Module.Free O T] [Module Z T] [IsScalarTower Z O T]
    {d : ℕ} (b : Module.Basis (Fin d) Z T) {ι : Type} [Fintype ι] (v : ι → R ⊗[O] T)
    (h1 : LinearIndependent R v) (h2 : Submodule.span R (Set.range v) = ⊤) :
    d = Module.finrank Z O * Fintype.card ι := by
  have e1 : Module.finrank Z T = d := by
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  have e2 : Module.finrank R (R ⊗[O] T) = Fintype.card ι :=
    Module.finrank_eq_card_basis (Module.Basis.mk h1 h2.ge)
  rw [← e1, ← e2, Module.finrank_baseChange, Module.finrank_mul_finrank]

theorem nontrivial_tensor_of_free {Z O S : Type} [CommRing Z] [CommRing O]
    [Nontrivial O] [Algebra Z O] [Module.Free Z O] [CommRing S] [Nontrivial S] [Algebra Z S] :
    Nontrivial (O ⊗[Z] S) := by
  haveI : Module.FaithfullyFlat Z O := inferInstance
  infer_instance

set_option synthInstance.maxHeartbeats 400000 in
theorem rank_count : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (d : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)) (ι : Type) [Fintype ι] (v : ι → TW (RW LL) T), IsMat K LL T M A → LinearIndependent (RW LL) v → Submodule.span (RW LL) (Set.range v) = ⊤ → ∃ (f : ℕ) (_ : Module.Basis (Fin f) ℤ_[l] ↥(OL LL)), Nonempty (Fin d ≃ Fin f × ι) := by
  intro l _ K LL T d M A ι _ v hM h1 h2
  haveI := freeOL LL
  haveI := finiteOL LL
  letI := zlMod LL T
  obtain ⟨b, -, -⟩ := hM
  haveI : Module.Free ↥(OL LL) ↥T.L.T := T.L.free
  haveI : IsScalarTower ℤ_[l] ↥(OL LL) ↥T.L.T := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  haveI : Nontrivial (RW LL) := nontrivial_tensor_of_free
  have h := card_eq_finrank_mul_card (R := RW LL) b v h1 h2
  refine ⟨Module.finrank ℤ_[l] ↥(OL LL), Module.finBasis _ _, ⟨Fintype.equivOfCardEq ?_⟩⟩
  simpa using h

end GlobalTheory.Cyc.Decomp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReductionSum
section
noncomputable section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps GlobalTheory.Present Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries
namespace GlobalTheory.Present.SumRed

section General
variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n₀ : ℕ}

theorem exists_proj {T T' Z : LocLat G Qp LL O} (f : LatHom T.L Z.L) (g : LatHom T'.L Z.L)
    (hb : Function.Bijective (f.f.coprod g.f))
    (hs : ∀ z ∈ Z.L.T, ∃ x ∈ T.L.T, ∃ y ∈ T'.L.T, z = f.f x + g.f y) :
    ∃ (p : LatHom Z.L T.L) (p' : LatHom Z.L T'.L), latAdd (latComp f p) (latComp g p') = latId Z := by
  let e : (T.V × T'.V) ≃ₗ[LL] Z.V := LinearEquiv.ofBijective _ hb
  have he : ∀ x y, e.symm (f.f x + g.f y) = (x, y) := fun x y => by
    rw [LinearEquiv.symm_apply_eq]; rfl
  have hz : ∀ z, f.f (e.symm z).1 + g.f (e.symm z).2 = z := fun z => e.apply_symm_apply z
  have hρ : ∀ σ z, e.symm (Z.ρ σ z) = (T.ρ σ (e.symm z).1, T'.ρ σ (e.symm z).2) := fun σ z => by
    rw [← he, f.equiv, g.equiv, ← map_add, hz]
  haveI := T.mtop.toContinuousSMul
  haveI := T'.mtop.toContinuousSMul
  refine ⟨⟨LinearMap.fst LL _ _ ∘ₗ e.symm.toLinearMap, fun σ z => ?_,
      IsModuleTopology.continuous_of_linearMap _, fun z h => ?_⟩,
    ⟨LinearMap.snd LL _ _ ∘ₗ e.symm.toLinearMap, fun σ z => ?_,
      IsModuleTopology.continuous_of_linearMap _, fun z h => ?_⟩, ?_⟩
  · exact congrArg Prod.fst (hρ σ z)
  · obtain ⟨x, hx, y, hy, rfl⟩ := hs z h
    change (e.symm _).1 ∈ _
    rw [he]; exact hx
  · exact congrArg Prod.snd (hρ σ z)
  · obtain ⟨x, hx, y, hy, rfl⟩ := hs z h
    change (e.symm _).2 ∈ _
    rw [he]; exact hy
  · unfold latAdd latId
    congr 1
    exact LinearMap.ext hz

variable (W : LocWach PD LL O v n₀)

theorem map_mem {T Z : LocLat G Qp LL O} (f : LatHom T.L Z.L) (x : ↥(DΔ W T)) :
    W.map f (x : W.DD T) ∈ DΔ W Z := fun δ hδ => by
  rw [← W.map_γ, x.2 δ hδ]

theorem red_sum {k : Type} [Field k] [Algebra O k] {l n : ℕ} {R : RingPG k l} {F : DFun R n G}
    {ι : k⸨X⸩ →ₐ[k] k⸨X⸩} {τ : ZMod n → ZMod n₀} {γ : W.Gam} (p : Pres W F ι τ γ)
    {T T' Z : LocLat G Qp LL O} {A A' C : Ob k G} {q q' r}
    (hq : Onto T A q) (hq' : Onto T' A' q') (hr : Onto Z C r)
    (hT : IsCrys PD T.ρ) (hT' : IsCrys PD T'.ρ) (hZ : IsCrys PD Z.ρ)
    (f : LatHom T.L Z.L) (g : LatHom T'.L Z.L) (a : (Fin A.m → k) →ₗ[k] (Fin C.m → k))
    (b : (Fin A'.m → k) →ₗ[k] (Fin C.m → k)) (hb : Function.Bijective (f.f.coprod g.f))
    (hs : ∀ z ∈ Z.L.T, ∃ x ∈ T.L.T, ∃ y ∈ T'.L.T, z = f.f x + g.f y) (ha : IsHom A C a) (hb' : IsHom A' C b)
    (hfa : ∀ (x : ↥T.L.T) (x' : ↥Z.L.T), (x' : Z.V) = f.f x → r x' = a (q x))
    (hgb : ∀ (x : ↥T'.L.T) (x' : ↥Z.L.T), (x' : Z.V) = g.f x → r x' = b (q' x))
    (N : Lats k n A.m) (N' : Lats k n A'.m) (L : Lats k n C.m)
    (hN : ∀ i y, y ∈ N i ↔ ∃ x : ↥(DΔ W T), (x : W.DD T) ∈ W.N T ∧ p.j T A q i x = y)
    (hN' : ∀ i y, y ∈ N' i ↔ ∃ x : ↥(DΔ W T'), (x : W.DD T') ∈ W.N T' ∧ p.j T' A' q' i x = y)
    (hL : ∀ i y, y ∈ L i ↔ ∃ x : ↥(DΔ W Z), (x : W.DD Z) ∈ W.N Z ∧ p.j Z C r i x = y) (i : ZMod n) :
    L i = F.push A C a N i ⊔ F.push A' C b N' i := by
  obtain ⟨π, π', hπ⟩ := exists_proj f g hb hs
  apply le_antisymm
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := (hL i y).1 hy
    let x₁ : ↥(DΔ W T) := ⟨_, map_mem W π x⟩
    let x₂ : ↥(DΔ W T') := ⟨_, map_mem W π' x⟩
    have hsum : x = ⟨_, map_mem W f x₁⟩ + ⟨_, map_mem W g x₂⟩ := by
      apply Subtype.ext
      have := W.map_id Z x
      rw [← hπ, W.map_latAdd, W.map_comp, W.map_comp] at this
      exact this.symm
    rw [hsum, map_add, p.j_map T A q Z C r hq hr f a ha hfa i x₁ _ rfl,
      p.j_map T' A' q' Z C r hq' hr g b hb' hgb i x₂ _ rfl]
    exact Submodule.add_mem_sup
      ⟨_, (hN i _).2 ⟨x₁, W.map_N π hZ hT _ hx, rfl⟩, rfl⟩
      ⟨_, (hN' i _).2 ⟨x₂, W.map_N π' hZ hT' _ hx, rfl⟩, rfl⟩
  · refine sup_le ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨x, hx, rfl⟩ := (hN i y).1 hy
      exact (hL i _).2 ⟨⟨_, map_mem W f x⟩, W.map_N f hT hZ _ hx,
        p.j_map T A q Z C r hq hr f a ha hfa i x _ rfl⟩
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨x, hx, rfl⟩ := (hN' i y).1 hy
      exact (hL i _).2 ⟨⟨_, map_mem W g x⟩, W.map_N g hT' hZ _ hx,
        p.j_map T' A' q' Z C r hq' hr g b hb' hgb i x _ rfl⟩

end General

theorem reduction_sum : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P) (S : TopSit P) (k : Type) [Field k] [Algebra S.O k] [CharP k l], S.IsRes k → ∀ {R : RingPG k l} (ι : k⸨X⸩ →ₐ[k] k⸨X⸩) (F : DFun R S.n S.G) (τ : ZMod S.n → ZMod (Module.finrank ℚ_[l] ↥(K0 S.K))) (γ : (S.W H).Gam) (p : Pres (S.W H) F ι τ γ), GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.IsCyclotomic R ι → (∀ i, (S.W H).emb (τ i) = S.emb i) → ((S.W H).χΓ γ : S.O) = 1 + (l : S.O) → GlobalTheory.WachUse.QN (S.W H) → ∀ (T : LocLat S.G ℚ_[l] ↥S.LL.1 S.O) (A : Ob k S.G) q (U : ZMod S.n → Multiset ℤ), Onto T A q → KerIs S.Γ.lam q → CrysWith (P.PD S.K) S.emb T.ρ U → ∀ (T' : LocLat S.G ℚ_[l] ↥S.LL.1 S.O) (A' : Ob k S.G) q' (U' : ZMod S.n → Multiset ℤ), Onto T' A' q' → KerIs S.Γ.lam q' → CrysWith (P.PD S.K) S.emb T'.ρ U' → ∀ (Z : LocLat S.G ℚ_[l] ↥S.LL.1 S.O) (C : Ob k S.G) r (V : ZMod S.n → Multiset ℤ), Onto Z C r → KerIs S.Γ.lam r → CrysWith (P.PD S.K) S.emb Z.ρ V → ∀ (f : LatHom T.L Z.L) (g : LatHom T'.L Z.L) (a : (Fin A.m → k) →ₗ[k] (Fin C.m → k)) (b : (Fin A'.m → k) →ₗ[k] (Fin C.m → k)), Function.Bijective (f.f.coprod g.f) → (∀ z ∈ Z.L.T, ∃ x ∈ T.L.T, ∃ y ∈ T'.L.T, z = f.f x + g.f y) → IsHom A C a → IsHom A' C b → (∀ (x : ↥T.L.T) (x' : ↥Z.L.T), (x' : Z.V) = f.f x → r x' = a (q x)) → (∀ (x : ↥T'.L.T) (x' : ↥Z.L.T), (x' : Z.V) = g.f x → r x' = b (q' x)) → ∀ (N : Lats k S.n A.m) (N' : Lats k S.n A'.m) (L : Lats k S.n C.m), (∀ i y, y ∈ N i ↔ ∃ x : ↥(DΔ (S.W H) T), (x : (S.W H).DD T) ∈ (S.W H).N T ∧ p.j T A q i x = y) → (∀ i y, y ∈ N' i ↔ ∃ x : ↥(DΔ (S.W H) T'), (x : (S.W H).DD T') ∈ (S.W H).N T' ∧ p.j T' A' q' i x = y) → (∀ i y, y ∈ L i ↔ ∃ x : ↥(DΔ (S.W H) Z), (x : (S.W H).DD Z) ∈ (S.W H).N Z ∧ p.j Z C r i x = y) → ∀ i, L i = F.push A C a N i ⊔ F.push A' C b N' i := by
  intro l _ P H S k _ _ _ _ R ι F τ γ p _ _ _ _ T A q U hq _ hT T' A' q' U' hq' _ hT' Z C r V hr _ hZ
    f g a b hb hs ha hb' hfa hgb N N' L hN hN' hL i
  exact red_sum (S.W H) p hq hq' hr hT.1 hT'.1 hZ.1 f g a b hb hs ha hb' hfa hgb N N' L hN hN' hL i

end GlobalTheory.Present.SumRed
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictionCorestrictionH1f
section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations TensorProduct

noncomputable section

namespace GlobalTheory.InducedSectionsSpanStatement

section General

variable {G G' : Type} [Group G] [TopologicalSpace G] [Group G'] [TopologicalSpace G']
    {Qp LL O : Type} [Field Qp] [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL]

def trCochain (ι : G →* G') [Fintype (G' ⧸ ι.range)] (T : LocLat G' Qp LL O) :
    (G → T.V) →ₗ[O] (G' → T.V) where
  toFun f g := ∑ q : G' ⧸ ι.range,
    T.ρ (g • q).out (f (Function.invFun ι ((g • q).out⁻¹ * g * q.out)))
  map_add' f f' := by
    funext g
    simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' a f := by
    funext g
    simp only [Pi.smul_apply, LinearMap.map_smul_of_tower, RingHom.id_apply, Finset.smul_sum]

theorem trCochain_apply (ι : G →* G') [Fintype (G' ⧸ ι.range)] (T : LocLat G' Qp LL O)
    (f : G → T.V) (g : G') : trCochain ι T f g = ∑ q : G' ⧸ ι.range,
    T.ρ (g • q).out (f (Function.invFun ι ((g • q).out⁻¹ * g * q.out))) := rfl

theorem trCochain_Z1T [IsTopologicalGroup G'] (ι : G →* G') (hι : Continuous ι)
    (he : Topology.IsEmbedding ι) (ho : IsOpen (ι.range : Set G')) [Fintype (G' ⧸ ι.range)]
    (T : LocLat G' Qp LL O) (c : G → T.V) (hc : c ∈ latticeCocycles (LiftingTheory.resLoc ι hι T).L) :
    trCochain ι T c ∈ latticeCocycles T.L := by
  obtain ⟨⟨hcont, hcoc⟩, hT⟩ := hc
  have hj : ∀ g, Function.invFun ι (ι g) = g := Function.leftInverse_invFun he.injective
  haveI : ContinuousSMul LL T.V := IsModuleTopology.toContinuousSMul LL T.V
  haveI : IsTopologicalAddGroup T.V := IsModuleTopology.topologicalAddGroup LL T.V
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · refine GlobalTheory.transfer_continuous_of_continuousOn LL G' T.V T.ρ ι.range ho
      (fun g => IsModuleTopology.continuous_of_linearMap (T.ρ g))
      (fun g => c (Function.invFun ι g)) ?_
    have h1 : (ι.range : Set G') = ι '' Set.univ := by
      rw [Set.image_univ]; rfl
    rw [h1, he.isInducing.continuousOn_image_iff]
    have h2 : ((fun g => c (Function.invFun ι g)) ∘ ι) = c := by
      funext g; simp only [Function.comp_apply, hj]
    rw [h2]
    exact hcont.continuousOn
  · refine (GlobalTheory.transfer_cocycle_formula LL G' T.V T.ρ ι.range).2.1
      (fun g => c (Function.invFun ι g)) ?_
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, hj, hj, hj]
    exact hcoc a b
  · intro g _
    rw [trCochain_apply]
    exact Submodule.sum_mem _ fun q _ => T.L.stable _ _ (hT _ (Set.mem_univ _))

theorem trCochain_B1T (ι : G →* G') (hι : Continuous ι) (hinj : Function.Injective ι)
    [Fintype (G' ⧸ ι.range)]
    (T : LocLat G' Qp LL O) (c : G → T.V) (hc : c ∈ latticeCoboundaries (LiftingTheory.resLoc ι hι T).L) :
    trCochain ι T c ∈ latticeCoboundaries T.L := by
  obtain ⟨x, hx, rfl⟩ := hc
  have hj : ∀ g, Function.invFun ι (ι g) = g := Function.leftInverse_invFun hinj
  refine ⟨∑ q : G' ⧸ ι.range, T.ρ q.out x,
    Submodule.sum_mem _ fun q _ => T.L.stable _ _ hx, ?_⟩
  funext g
  symm
  refine (GlobalTheory.transfer_cocycle_formula LL G' T.V T.ρ ι.range).2.2.1
    (fun g => T.ρ (ι (Function.invFun ι g)) x - x) x ?_ g
  rintro _ ⟨a, rfl⟩
  rw [hj]

def corH1 [IsTopologicalGroup G'] (ι : G →* G') (hι : Continuous ι)
    (he : Topology.IsEmbedding ι) (ho : IsOpen (ι.range : Set G')) [Fintype (G' ⧸ ι.range)]
    (T : LocLat G' Qp LL O) : LatticeCohomology (LiftingTheory.resLoc ι hι T).L →ₗ[O] LatticeCohomology T.L :=
  Submodule.mapQ _ _
    (((trCochain ι T).comp (latticeCocycles (LiftingTheory.resLoc ι hι T).L).subtype).codRestrict (latticeCocycles T.L)
      (fun c => trCochain_Z1T ι hι he ho T c c.2))
    (by
      intro c hc
      simp only [Submodule.mem_comap, Submodule.subtype_apply] at hc ⊢
      exact trCochain_B1T ι hι he.injective T c hc)

theorem corH1_res [IsTopologicalGroup G'] (ι : G →* G') (hι : Continuous ι)
    (he : Topology.IsEmbedding ι) (ho : IsOpen (ι.range : Set G')) [Fintype (G' ⧸ ι.range)]
    (T : LocLat G' Qp LL O) (κ : LatticeCohomology T.L) :
    corH1 ι hι he ho T (LiftingTheory.resH1 ι hι T κ) = ((ι.range.index : ℕ) : O) • κ := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ κ
  rw [← Submodule.Quotient.mk_smul]
  refine (Submodule.Quotient.eq _).2 ?_
  obtain ⟨c, ⟨hcont, hcoc⟩, hT⟩ := c
  refine ⟨∑ q : G' ⧸ ι.range, c q.out,
    Submodule.sum_mem _ fun q _ => hT _ (Set.mem_univ _), ?_⟩
  funext g
  have H := GlobalTheory.transfer_cocycle_formula LL G' T.V T.ρ ι.range
  have h4 := H.2.2.2 c hcoc g
  have hj : ∀ q : G' ⧸ ι.range, ι (Function.invFun ι ((g • q).out⁻¹ * g * q.out))
      = (g • q).out⁻¹ * g * q.out := fun q => Function.invFun_eq (H.1 g q)
  change T.ρ g (∑ q : G' ⧸ ι.range, c q.out) - ∑ q : G' ⧸ ι.range, c q.out
    = ∑ q : G' ⧸ ι.range, T.ρ (g • q).out
        (c (ι (Function.invFun ι ((g • q).out⁻¹ * g * q.out)))) - ((ι.range.index : ℕ) : O) • c g
  simp only [hj]
  simp only at h4
  rw [h4, Nat.cast_smul_eq_nsmul]
  abel

theorem corH1_natural [IsTopologicalGroup G'] (ι : G →* G') (hι : Continuous ι)
    (he : Topology.IsEmbedding ι) (ho : IsOpen (ι.range : Set G')) [Fintype (G' ⧸ ι.range)]
    (T₁ T₂ : LocLat G' Qp LL O) (F : LatHom T₁.L T₂.L) (κ : LatticeCohomology (LiftingTheory.resLoc ι hι T₁).L) :
    corH1 ι hι he ho T₂ ((LiftingTheory.resHom ι hι F).H1map κ) = F.H1map (corH1 ι hι he ho T₁ κ) := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ κ
  refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
  funext g
  change ∑ q : G' ⧸ ι.range, T₂.ρ (g • q).out
        (F.f (c.1 (Function.invFun ι ((g • q).out⁻¹ * g * q.out))))
    = F.f (∑ q : G' ⧸ ι.range, T₁.ρ (g • q).out
        (c.1 (Function.invFun ι ((g • q).out⁻¹ * g * q.out))))
  rw [map_sum]
  exact Finset.sum_congr rfl fun q _ => (F.equiv _ _).symm

variable {K₀ K K₀' K' : Type} [Field K₀] [Field K] [Field K₀'] [Field K']
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    [Algebra Qp K₀'] [Algebra Qp K'] [Algebra K₀' K'] [IsScalarTower Qp K₀' K']
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    [Algebra K₀' B] [IsScalarTower Qp K₀' B] [Algebra K₀' BdR] [Algebra K' BdR]
    [IsScalarTower Qp K' BdR] [IsScalarTower K₀' K' BdR] [IsScalarTower Qp K₀' BdR]

def repVB (PD' : PeriodData G' Qp K₀' K' B BdR) (T : LocLat G' Qp LL O) :
    Representation LL G' (T.V ⊗[Qp] B) where
  toFun g := actVB PD' T.ρ g
  map_one' := by
    refine AlgebraTensorModule.curry_injective ?_
    ext x b
    simp [actVB]
  map_mul' g h := by
    refine AlgebraTensorModule.curry_injective ?_
    ext x b
    simp [actVB]

theorem actVB_tmul_one (PD' : PeriodData G' Qp K₀' K' B BdR) (T : LocLat G' Qp LL O) (g : G')
    (x : T.V) : actVB PD' T.ρ g (x ⊗ₜ[Qp] (1 : B)) = T.ρ g x ⊗ₜ[Qp] (1 : B) := by
  simp [actVB]

theorem actVB_res (PD : PeriodData G Qp K₀ K B BdR) (PD' : PeriodData G' Qp K₀' K' B BdR)
    (ι : G →* G') (hι : Continuous ι) (hact : ∀ g b, PD.actB g b = PD'.actB (ι g) b)
    (T : LocLat G' Qp LL O) (g : G) (x : T.V ⊗[Qp] B) :
    actVB PD (LiftingTheory.resLoc ι hι T).ρ g x = actVB PD' T.ρ (ι g) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVB, hact]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem coreCor_of_isOpen [IsTopologicalGroup G'] (PD : PeriodData G Qp K₀ K B BdR)
    (PD' : PeriodData G' Qp K₀' K' B BdR) (ι : G →* G') (hι : Continuous ι)
    (he : Topology.IsEmbedding ι) (ho : IsOpen (ι.range : Set G')) [ι.range.FiniteIndex]
    (hact : ∀ g b, PD.actB g b = PD'.actB (ι g) b) :
    LiftingTheory.coreCor PD PD' LL O ι hι ι.range.index := by
  haveI : Fintype (G' ⧸ ι.range) := Fintype.ofFinite _
  refine ⟨?_, corH1 ι hι he ho, corH1_res ι hι he ho, ?_, corH1_natural ι hι he ho⟩
  · rintro T _ ⟨c, ⟨hc, hc', x, hx⟩, rfl⟩
    have hz := LiftingTheory.resFun_Z1T ι hι T c c.2
    refine ⟨⟨LiftingTheory.resFun ι T c, hz⟩, ⟨hz, hz.1, x, fun g => ?_⟩, rfl⟩
    rw [actVB_res PD PD' ι hι hact]
    exact hx (ι g)
  · rintro T _ ⟨c, ⟨hc, hc', x, hx⟩, rfl⟩
    have hz := trCochain_Z1T ι hι he ho T c c.2
    have hj : ∀ g, Function.invFun ι (ι g) = g := Function.leftInverse_invFun he.injective
    refine ⟨⟨trCochain ι T c, hz⟩,
      ⟨hz, hz.1, ∑ q : G' ⧸ ι.range, actVB PD' T.ρ q.out x, fun g => ?_⟩, rfl⟩
    have h3 := (GlobalTheory.transfer_cocycle_formula LL G' _ (repVB PD' T) ι.range).2.2.1
      (fun g => c.1 (Function.invFun ι g) ⊗ₜ[Qp] (1 : B)) x (by
        rintro _ ⟨a, rfl⟩
        have := hx a
        rw [actVB_res PD PD' ι hι hact] at this
        rw [hj]
        exact this) g
    refine Eq.trans ?_ h3
    change trCochain ι T c g ⊗ₜ[Qp] (1 : B) = _
    rw [trCochain_apply, sum_tmul]
    exact Finset.sum_congr rfl fun q _ => (actVB_tmul_one PD' T _ _).symm

end General

open Formalism.BasicNotions.Loc

theorem GK_index_eq_finrank {l : ℕ} [Fact l.Prime] (K : FinExt l) :
    (GK K).index = Module.finrank ℚ_[l] ↥K.1 :=
  (IntermediateField.finrank_eq_fixingSubgroup_index (Om l) K.1).symm

theorem inclusion_GK_index {l : ℕ} [Fact l.Prime] (K K' : FinExt l) (hle : GK K ≤ GK K') :
    (Subgroup.inclusion hle).range.index * Module.finrank ℚ_[l] ↥K'.1
      = Module.finrank ℚ_[l] ↥K.1 := by
  rw [Subgroup.inclusion_range, ← GK_index_eq_finrank, ← GK_index_eq_finrank]
  exact Subgroup.relIndex_mul_index hle

end GlobalTheory.InducedSectionsSpanStatement

namespace GlobalTheory

open Formalism.BasicNotions.Loc

theorem res_cor_H1f : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW),
    LiftingTheory.adm20 D HW F := by
  intro D HW F l _ K K' _ hle LL
  haveI := K.2
  haveI := K'.2
  have hidx := InducedSectionsSpanStatement.inclusion_GK_index K K' hle
  have hpos : 0 < Module.finrank ℚ_[l] ↥K.1 := Module.finrank_pos
  have hpos' : 0 < Module.finrank ℚ_[l] ↥K'.1 := Module.finrank_pos
  have hg : Module.finrank ℚ_[l] ↥K.1 / Module.finrank ℚ_[l] ↥K'.1
      = (Subgroup.inclusion hle).range.index := by
    rw [← hidx, Nat.mul_div_cancel _ hpos']
  haveI : (Subgroup.inclusion hle).range.FiniteIndex := ⟨fun h => by
    rw [h, zero_mul] at hidx; omega⟩
  rw [hg]
  refine InducedSectionsSpanStatement.coreCor_of_isOpen _ _ _ _ (Topology.IsEmbedding.inclusion hle) ?_ ?_
  · rw [Subgroup.inclusion_range]
    exact (IntermediateField.fixingSubgroup_isOpen K.1).preimage continuous_subtype_val
  · intro g b
    rw [(D.loc l).PD_actB, (D.loc l).PD_actB]
    rfl

end GlobalTheory
end
end

