import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0121
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraMapConeRing
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SEqOne
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0001
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0123
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0049
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PairSums.SumPair
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised
import ReciprocityTheory.Hypotheses.GalCoh

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConsequenceOfMackeyStatement
section
open ReciprocityTheory.Ty.Fin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.consequence_of_mackey : ReciprocityTheory.Ty.Fin.St.FromMackey := by
  first | exact @GlobalTheory.CompanionTheory.TyFin.FromMackey.fromMackey | exact GlobalTheory.CompanionTheory.TyFin.FromMackey.fromMackey | (intros; apply GlobalTheory.CompanionTheory.TyFin.FromMackey.fromMackey <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExPOfCompatibleEquiv
section
set_option autoImplicit false
namespace GlobalTheory.CompanionTheory.SurjectionOntoH4
open CrystallineSemistableComparison.Onto

theorem dZ_addEquiv_apply {ι : Type} [DecidableEq ι] (M N : Finset ι → Type) [∀ S, AddCommGroup (M S)]
    [∀ S, AddCommGroup (N S)] (r : ∀ {S T : Finset ι}, S ⊆ T → M S → M T)
    (r' : ∀ {S T : Finset ι}, S ⊆ T → N S → N T) (e : ∀ S, M S ≃+ N S)
    (hn : ∀ {S T : Finset ι} (h : S ⊆ T) x, e T (r h x) = r' h (e S x)) (m : ℕ)
    (c : ∀ i : Fin (m + 1) → ι, M (ent i)) (i : Fin (m + 2) → ι) :
    e _ (dZ M r m c i) = dZ N r' m (fun i => e _ (c i)) i := by
  simp only [dZ, map_sum, map_zsmul, hn]

theorem dZ_eq_zero_of_addEquiv {ι : Type} [DecidableEq ι] (M N : Finset ι → Type) [∀ S, AddCommGroup (M S)]
    [∀ S, AddCommGroup (N S)] (r : ∀ {S T : Finset ι}, S ⊆ T → M S → M T)
    (r' : ∀ {S T : Finset ι}, S ⊆ T → N S → N T) (e : ∀ S, M S ≃+ N S)
    (hn : ∀ {S T : Finset ι} (h : S ⊆ T) x, e T (r h x) = r' h (e S x)) (m : ℕ)
    (c : ∀ i : Fin (m + 1) → ι, N (ent i)) (hc : dZ N r' m c = 0) :
    dZ M r m (fun i => (e _).symm (c i)) = 0 := by
  funext i
  apply (e _).injective
  rw [dZ_addEquiv_apply M N r r' e hn m, Pi.zero_apply, map_zero]
  simp only [AddEquiv.apply_symm_apply]
  exact congrFun hc i

theorem exP_of_addEquiv : ∀ {ι : Type} [DecidableEq ι] (M N : Finset ι → Type) [∀ S, AddCommGroup (M S)] [∀ S, AddCommGroup (N S)] (r : ∀ {S T : Finset ι}, S ⊆ T → M S → M T) (r' : ∀ {S T : Finset ι}, S ⊆ T → N S → N T) (e : ∀ S, M S ≃+ N S), (∀ {S T : Finset ι} (h : S ⊆ T) x, e T (r h x) = r' h (e S x)) → ExP M r → ExP N r' := by
  intro ι _ M N _ _ r r' e hn hM
  obtain ⟨h0, h1, h2⟩ := hM
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    have hx' : (e ∅).symm x = 0 := by
      apply h0
      intro i
      have h7 := hn (Finset.empty_subset (ent i)) ((e ∅).symm x)
      rw [AddEquiv.apply_symm_apply] at h7
      have h8 : r' (Finset.empty_subset (ent i)) x = 0 := hx i
      rw [h8] at h7
      exact (e _).injective (h7.trans (map_zero _).symm)
    simpa using congrArg (e ∅) hx'
  · intro c hc
    obtain ⟨x, hx⟩ := h1 (fun i => (e _).symm (c i)) (dZ_eq_zero_of_addEquiv M N r r' e hn 0 c hc)
    refine ⟨e ∅ x, fun i => ?_⟩
    have h5 : r (Finset.empty_subset (ent i)) x = (e _).symm (c i) := hx i
    have h6 := hn (Finset.empty_subset (ent i)) x
    rw [h5, AddEquiv.apply_symm_apply] at h6
    exact h6.symm
  · intro m c hc
    obtain ⟨b, hb⟩ := h2 m (fun i => (e _).symm (c i)) (dZ_eq_zero_of_addEquiv M N r r' e hn (m + 1) c hc)
    refine ⟨fun i => e _ (b i), ?_⟩
    funext i
    have h3 := dZ_addEquiv_apply M N r r' e hn m b i
    have h4 : dZ M r m b i = (e _).symm (c i) := congrFun hb i
    rw [h4, AddEquiv.apply_symm_apply] at h3
    exact h3.symm

end GlobalTheory.CompanionTheory.SurjectionOntoH4
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExceptionalIdealLeSpanPosDegree
section
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.SurjectionOntoH4
open CrystallineSemistableComparison.Onto

theorem single_mul_mem_span_tdeg_pos {K : Type} [Field K] {n d : ℕ} (S : Finset (Fin d))
    (m : (cone S : AddSubmonoid (Gam n d))) (a : K) (x : R0 K n d S)
    (hx : x ∈ Submodule.span K {y : R0 K n d S | ∃ (g : Gam n d) (hg : g ∈ (cone S : AddSubmonoid (Gam n d))),
      1 ≤ tdeg g ∧ y = mon K g hg}) :
    (AddMonoidAlgebra.single m a : R0 K n d S) * x ∈ Submodule.span K {y : R0 K n d S |
      ∃ (g : Gam n d) (hg : g ∈ (cone S : AddSubmonoid (Gam n d))), 1 ≤ tdeg g ∧ y = mon K g hg} := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨g, hg, h1, rfl⟩ := hy
    have e : (AddMonoidAlgebra.single m a : R0 K n d S) * mon K g hg =
        a • mon K (m.1 + g) ((cone S : AddSubmonoid (Gam n d)).add_mem m.2 hg) := by
      simp only [mon, AddMonoidAlgebra.single_mul_single, mul_one, AddMonoidAlgebra.smul_single, smul_eq_mul]
      rfl
    rw [e]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, _, ?_, rfl⟩)
    have h0 : 0 ≤ tdeg m.1 := m.2.2.2
    rw [tdeg_add]
    linarith
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ _ hx

theorem exceptional_ideal_le_span_pos_degree : ∀ {K : Type} [Field K] {n d : ℕ} (S : Finset (Fin d)) (x : R0 K n d S),
    x ∈ I0 n K S → x ∈ Submodule.span K {y : R0 K n d S |
      ∃ (g : Gam n d) (hg : g ∈ (cone S : AddSubmonoid (Gam n d))), 1 ≤ tdeg g ∧ y = mon K g hg} := by
  intro K _ n d S x hx
  unfold I0 Ideal.span at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨k, _, rfl⟩ := hy
    exact Submodule.subset_span ⟨_, _, by rw [tdeg_oneE_inr], rfl⟩
  | zero => exact Submodule.zero_mem _
  | add x y _ _ hx hy => exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [smul_eq_mul]
    induction c using AddMonoidAlgebra.induction_linear with
    | zero => rw [zero_mul]; exact Submodule.zero_mem _
    | add f g hf hg => rw [add_mul]; exact Submodule.add_mem _ hf hg
    | single m a => exact single_mul_mem_span_tdeg_pos S m a x hx

end GlobalTheory.CompanionTheory.SurjectionOntoH4
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsDualDerivationsOfCoords
section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.ConeDerivs

theorem exists_dual_derivations : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    (V : X.Opens) (d : ℕ) (c : Coord q V d), letI := (strV q V).toAlgebra;
    ∃ D : Fin d → Derivation K Γ(X, V) Γ(X, V), ∀ k j, D k (c.t j) = if k = j then 1 else 0 := by
  intro K _ X q V d c
  letI := (strV q V).toAlgebra
  letI : Algebra (MvPolynomial (Fin d) K) Γ(X, V) :=
    (MvPolynomial.eval₂Hom (strV q V) c.t : MvPolynomial (Fin d) K →+* Γ(X, V)).toAlgebra
  haveI : IsScalarTower K (MvPolynomial (Fin d) K) Γ(X, V) :=
    IsScalarTower.of_algebraMap_eq fun r => (MvPolynomial.eval₂Hom_C (strV q V) c.t r).symm
  haveI : Algebra.Etale (MvPolynomial (Fin d) K) Γ(X, V) := c.etale
  obtain ⟨⟨b, hb⟩, -⟩ := GlobalTheory.EtaleCoordJacobian.exists_basis_of_etale K Γ(X, V) (Fin d)
  have hb' : ∀ j, KaehlerDifferential.D K Γ(X, V) (c.t j) = b j := fun j => by
    rw [hb j]
    congr 1
    exact (MvPolynomial.eval₂Hom_X' (strV q V) c.t j).symm
  refine ⟨fun k => KaehlerDifferential.linearMapEquivDerivation K Γ(X, V)
    (b.coord k), fun k j => ?_⟩
  change b.coord k (KaehlerDifferential.D K Γ(X, V) (c.t j)) = _
  rw [hb', Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  simp only [eq_comm]

end GlobalTheory.CompanionTheory.ConeDerivs
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsHermitianCongrToOneStatement
section
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hermitian_congr_to_one : ∀ (E : Type) [CommRing E] (τ : E →+* E) (q : ℕ) (ε : ℤ), ResAlg E τ q ε → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E), cT τ T = T → IsUnit T.det → ∃ g : Matrix (Fin n) (Fin n) E, IsUnit g.det ∧ cT τ g * T * g = 1 := by
  first | exact @GlobalTheory.CompanionTheory.UnrDens.exists_congr_one | exact GlobalTheory.CompanionTheory.UnrDens.exists_congr_one | (intros; apply GlobalTheory.CompanionTheory.UnrDens.exists_congr_one <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsMulPowEqIncl
section
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CompanionTheory.SurjectionOntoH4.Away

variable {K : Type} [Field K] {n d : ℕ}

theorem mon_pow {M : AddSubmonoid (Gam n d)} (c : Gam n d) (hc : c ∈ M) (N : ℕ) :
    mon K c hc ^ N = mon K (N • c) (M.nsmul_mem hc N) := by
  simp only [mon, AddMonoidAlgebra.single_pow, one_pow]
  rfl

theorem incl_injective {M M' : AddSubmonoid (Gam n d)} (h : M ≤ M') :
    Function.Injective (incl (K := K) h) := by
  intro x y hxy
  simp only [incl, AddMonoidAlgebra.mapDomainAlgHom_apply] at hxy
  exact AddMonoidAlgebra.mapDomain_injective (AddSubmonoid.inclusion_injective h) hxy

theorem exists_mul_pow_eq_incl {M M' : AddSubmonoid (Gam n d)} (h : M ≤ M') (c : Gam n d) (hc : c ∈ M)
    (hg : ∀ g ∈ M', ∃ N : ℕ, g + N • c ∈ M) (z : Rg K M') :
    ∃ (N : ℕ) (a : Rg K M), z * incl h (mon K c hc ^ N) = incl h a := by
  induction z using AddMonoidAlgebra.induction_linear with
  | zero => exact ⟨0, 0, by simp⟩
  | add f g hf hg' =>
    obtain ⟨N₁, a₁, h₁⟩ := hf
    obtain ⟨N₂, a₂, h₂⟩ := hg'
    refine ⟨N₁ + N₂, a₁ * mon K c hc ^ N₂ + a₂ * mon K c hc ^ N₁, ?_⟩
    rw [map_add, map_mul, map_mul, ← h₁, ← h₂, pow_add, map_mul]
    ring
  | single m k =>
    obtain ⟨N, hN⟩ := hg m.1 m.2
    refine ⟨N, AddMonoidAlgebra.single ⟨m.1 + N • c, hN⟩ k, ?_⟩
    rw [mon_pow, incl_mon]
    simp only [mon, incl, AddMonoidAlgebra.mapDomainAlgHom_apply, AddMonoidAlgebra.single_mul_single, mul_one]
    simp
    rfl

theorem isLocalization_away : ∀ {K : Type} [Field K] {n d : ℕ} {M M' : AddSubmonoid (Gam n d)} (h : M ≤ M') (c : Gam n d) (hc : c ∈ M), -c ∈ M' → (∀ g ∈ M', ∃ N : ℕ, g + N • c ∈ M) → letI := (incl (K := K) h).toRingHom.toAlgebra; IsLocalization.Away (mon K c hc) (Rg K M') := by
  intro K _ n d M M' h c hc hneg hg
  letI := (incl (K := K) h).toRingHom.toAlgebra
  have hal : ∀ x, algebraMap (Rg K M) (Rg K M') x = incl h x := fun _ => rfl
  have hu : IsUnit (incl h (mon K c hc)) := by
    rw [incl_mon]
    refine IsUnit.of_mul_eq_one (mon K (-c) hneg) ?_
    rw [mon_mul]
    simp only [mon, add_neg_cancel]
    rfl
  refine (isLocalization_iff _ _).2 ⟨?_, fun z => ?_, fun {x y} hxy => ⟨1, ?_⟩⟩
  · rintro ⟨_, N, rfl⟩
    rw [hal, map_pow]
    exact hu.pow N
  · obtain ⟨N, a, ha⟩ := exists_mul_pow_eq_incl h c hc hg z
    exact ⟨(a, ⟨mon K c hc ^ N, N, rfl⟩), ha⟩
  · rw [incl_injective h hxy]

end GlobalTheory.CompanionTheory.SurjectionOntoH4.Away
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPrimitiveRootOfIsAlgClosure
section
noncomputable section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.S2pt

namespace GlobalTheory.CompanionTheory.GreenbergWiles

theorem exists_primitiveRoot_of_isAlgClosure (F Ω : Type) [Field F] [NumberField F] [Field Ω]
    [Algebra F Ω] [IsAlgClosure F Ω] (n : ℕ) (hn : 0 < n) : ∃ ζ : Ω, IsPrimitiveRoot ζ n := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : NeZero (n : Ω) := ⟨Nat.cast_ne_zero.2 hn.ne'⟩
  exact HasEnoughRootsOfUnity.exists_primitiveRoot Ω n

theorem poitouTate_instance : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (S : Finset (HeightOneSpectrum (𝓞 F))) (Av : S → ValuationSubring Ω) (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ) (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M) (hρ : ContAction ρ), ∀ hμ : μ.comp (toGS Ω _) = cycMod F Ω l r, PoitouTateNormalised → l ≠ 2 → 0 < r → ContainsAbove S l → (∀ v : S, IsPlaceOver (Av v) v.1) → ∃ inv : InvFam F Ω l r, (∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v → Function.Bijective (inv A)) ∧ NineTermExact S Av μ (invAt S Av μ hμ inv) ρ hρ ∧ ShaDual S Av μ ρ := by
  intro F Ω _ _ _ _ _ l _ r M _ _ _ _ _ S Av μ ρ hρ hμ hPT hl hr hS hAv
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_of_isAlgClosure F Ω (l ^ r)
    (pow_pos (Fact.out : l.Prime).pos r)
  obtain ⟨inv, h1, h2⟩ := hPT F Ω l r (Or.inl hl) hr ζ hζ
  obtain ⟨hN, hD, -⟩ := h2 S hS Av hAv μ hμ M ρ hρ
  exact ⟨inv, fun A v h => (h1 A v h).1, hN, hD⟩

end GlobalTheory.CompanionTheory.GreenbergWiles

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreRepresentationSmooth
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology

namespace GlobalTheory.CompanionTheory.ThetaGLLen

section Smooth

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable (a c d : Type) [Fintype a] [DecidableEq a] [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]

theorem isSmoothChar_fibChar {μ : kˣ →* ℂˣ} (hμ : IsSmoothChar μ) :
    IsSmoothChar (fibChar (k := k) a c d μ) := by
  have hA : ∀ s : ℂ, IsSmoothChar (absPow k s) := fun s => isSmoothChar_of_isUnram (isUnram_absPow k s)
  refine IsSmoothChar.mul (IsSmoothChar.mul ?_ ?_) ?_
  · exact (IsSmoothChar.detChar (hμ.inv.mul (hA _))).comp _ continuous_fst
  · exact (IsSmoothChar.detChar ((hμ.mul (hA _)).mul (hA _))).comp _ (continuous_fst.comp continuous_snd)
  · exact (IsSmoothChar.detChar ((hμ.mul (hA _)).mul (hA _))).comp _ (continuous_snd.comp continuous_snd)

private theorem isSmooth_sbRep_of_continuous_action {Γ X : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [TopologicalSpace X] (r : X → Γ → X) (h1 : ∀ x, r x 1 = x)
    (hm : ∀ (x : X) (g h : Γ), r x (g * h) = r (r x g) h)
    (hc : ∀ g, Continuous fun x => r x g) (hj : Continuous fun p : X × Γ => r p.1 p.2) :
    IsSmooth (GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.sbRep r h1 hm hc) := by
  apply GlobalTheory.SmGL.isSmooth_of_nhds
  intro φ
  obtain ⟨hlc, hcs⟩ := φ.2
  have hopen : IsOpen {z : Γ × X | (φ : X → ℂ) (r z.2 z.1) = (φ : X → ℂ) z.2} := by
    have h1lc : IsLocallyConstant (fun z : Γ × X => (φ : X → ℂ) (r z.2 z.1)) :=
      hlc.comp_continuous (hj.comp continuous_swap)
    have h2lc : IsLocallyConstant (fun z : Γ × X => (φ : X → ℂ) z.2) :=
      hlc.comp_continuous continuous_snd
    have := (h1lc.comp₂ h2lc (fun u v => u - v)).isOpen_fiber 0
    simpa only [sub_eq_zero] using this
  have hev : ∀ᶠ γ in 𝓝 (1 : Γ), ∀ x ∈ tsupport (φ : X → ℂ), (φ : X → ℂ) (r x γ) = (φ : X → ℂ) x := by
    refine IsCompact.eventually_forall_of_forall_eventually hcs ?_
    intro x _
    exact hopen.mem_nhds (by simp only [Set.mem_ofPred_eq, h1])
  have hev' : ∀ᶠ γ in 𝓝 (1 : Γ), ∀ x ∈ tsupport (φ : X → ℂ),
      (φ : X → ℂ) (r x γ⁻¹) = (φ : X → ℂ) x := by
    have ht : Filter.Tendsto (fun γ : Γ => γ⁻¹) (𝓝 1) (𝓝 1) := by
      simpa using (continuous_inv.tendsto (1 : Γ))
    exact ht.eventually hev
  filter_upwards [hev, hev'] with γ hγ hγ'
  apply Subtype.ext
  funext x
  show (φ : X → ℂ) (r x γ) = (φ : X → ℂ) x
  by_cases hx : x ∈ tsupport (φ : X → ℂ)
  · exact hγ x hx
  · by_cases hy : r x γ ∈ tsupport (φ : X → ℂ)
    · have e := hγ' _ hy
      rw [← hm, mul_inv_cancel, h1] at e
      exact e.symm
    · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hy]

private theorem isSmooth_fibBase (κ : ℕ) : IsSmooth (fibBase (k := k) a c κ) := by
  show IsSmooth (GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.sbRep _ _ _ _)
  apply isSmooth_sbRep_of_continuous_action
  apply Continuous.subtype_mk
  have hinv : Continuous fun p : GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.RankIn k a c {κ} × (GL a k × GL c k) =>
      (((p.2.2)⁻¹ : GL c k) : Matrix c c k) :=
    Units.continuous_val.comp (continuous_inv.comp (continuous_snd.comp continuous_snd))
  have hx : Continuous fun p : GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.RankIn k a c {κ} × (GL a k × GL c k) =>
      (p.1 : Matrix c a k) :=
    continuous_subtype_val.comp continuous_fst
  have hg : Continuous fun p : GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences.RankIn k a c {κ} × (GL a k × GL c k) =>
      ((p.2.1 : GL a k) : Matrix a a k) :=
    Units.continuous_val.comp (continuous_fst.comp continuous_snd)
  exact (hinv.matrix_mul hx).matrix_mul hg

theorem isSmooth_fibRep_levi (μ : kˣ →* ℂˣ) (hμ : IsSmoothChar μ) (κ : ℕ) :
    IsSmooth ((fibRep (k := k) a c d μ κ).comp (MonoidHom.inr (GL a k) (GL c k × GL d k))) := by
  have hB := isSmooth_fibBase (k := k) a c κ
  have hρ := isSmooth_comp hB ((MonoidHom.id (GL a k)).prodMap (MonoidHom.fst (GL c k) (GL d k)))
    (continuous_id.prodMap continuous_fst)
  have ht := isSmooth_twist hρ (isSmoothChar_fibChar a c d hμ)
  exact isSmooth_comp ht (MonoidHom.inr (GL a k) (GL c k × GL d k)) (continuous_const.prodMk continuous_id)

end Smooth

end GlobalTheory.CompanionTheory.ThetaGLLen

namespace GlobalTheory.CompanionTheory.ThetaGLLen

theorem isSmooth_fibRep_inr : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (a c d : Type) [Fintype a] [DecidableEq a] [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d] (μ : kˣ →* ℂˣ), IsSmoothChar μ → ∀ κ : ℕ, IsSmooth ((fibRep (k := k) a c d μ κ).comp (MonoidHom.inr (GL a k) (GL c k × GL d k))) := by
  intro k _ _ _ _ a c d _ _ _ _ _ _ μ hμ κ
  exact isSmooth_fibRep_levi a c d μ hμ κ

end GlobalTheory.CompanionTheory.ThetaGLLen
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteDualInjectiveEquivStatement
section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_dual_injective_equiv : ∀ (n : ℕ) [NeZero n] (X Y : Type) [AddCommGroup X] [Module (ZMod n) X] [Finite X] [AddCommGroup Y] [Module (ZMod n) Y] [Finite Y], (∃ f : Y →ₗ[ZMod n] Module.Dual (ZMod n) X, Function.Injective f) → (∃ g : X →ₗ[ZMod n] Module.Dual (ZMod n) Y, Function.Injective g) → Nonempty (Y ≃ₗ[ZMod n] Module.Dual (ZMod n) X) ∧ Nat.card X = Nat.card Y := by
  first | exact @GlobalTheory.CompanionTheory.ZModDual.equiv_dual_of_injective_pair | exact GlobalTheory.CompanionTheory.ZModDual.equiv_dual_of_injective_pair | (intros; apply GlobalTheory.CompanionTheory.ZModDual.equiv_dual_of_injective_pair <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteLengthCoinvariantsExact
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences GlobalTheory.RankStrataProof GlobalTheory.CompanionTheory.ThetaGLLen Matrix Topology

namespace GlobalTheory.CompanionTheory.CoinvExact

theorem hasFiniteLength_of_exact {G A B C : Type} [Group G] [AddCommGroup A] [Module ℂ A]
    [AddCommGroup B] [Module ℂ B] [AddCommGroup C] [Module ℂ C]
    (α : Representation ℂ G A) (β : Representation ℂ G B) (γ : Representation ℂ G C)
    (f : α.IntertwiningMap β) (g : β.IntertwiningMap γ)
    (hg : Function.Surjective g) (hfg : Function.Exact f g)
    (hA : HasFiniteLength α) (hC : HasFiniteLength γ) : HasFiniteLength β := by
  let f' := Representation.IntertwiningMap.equivLinearMapAsModule α β f
  let g' := Representation.IntertwiningMap.equivLinearMapAsModule β γ g
  have hg' : Function.Surjective g' := hg
  have hr : IsFiniteLength (MonoidAlgebra ℂ G) (LinearMap.range f') :=
    IsFiniteLength.of_surjective hA f'.surjective_rangeRestrict
  have hex : Function.Exact (LinearMap.range f').subtype g' := by
    intro y
    have h1 : g' y = 0 ↔ g y = 0 := Iff.rfl
    have h2 : y ∈ Set.range (LinearMap.range f').subtype ↔ y ∈ Set.range f := by
      constructor
      · rintro ⟨⟨_, ⟨a, rfl⟩⟩, rfl⟩
        exact ⟨a, rfl⟩
      · rintro ⟨a, rfl⟩
        exact ⟨⟨f' a, ⟨a, rfl⟩⟩, rfl⟩
    rw [h1, h2]
    exact hfg y
  have hlen := Module.length_eq_add_of_exact (LinearMap.range f').subtype g'
    (LinearMap.range f').injective_subtype hg' hex
  rw [HasFiniteLength, ← Module.length_ne_top_iff, hlen]
  exact WithTop.add_ne_top.2 ⟨Module.length_ne_top_iff.2 hr, Module.length_ne_top_iff.2 hC⟩

section Coinv

variable {Γ G V₁ V₂ : Type} [Group Γ] [Group G] [AddCommGroup V₁] [Module ℂ V₁]
  [AddCommGroup V₂] [Module ℂ V₂] {τ₁ : Representation ℂ (Γ × G) V₁} {τ₂ : Representation ℂ (Γ × G) V₂}

theorem twRel_le_comap (φ : τ₁.IntertwiningMap τ₂) (ψ : Γ →* ℂˣ) :
    twRel (τ₁.comp (MonoidHom.inl Γ G)) ψ ≤
      (twRel (τ₂.comp (MonoidHom.inl Γ G)) ψ).comap φ.toLinearMap := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨γ, v, rfl⟩
  refine Submodule.subset_span ⟨γ, φ v, ?_⟩
  have e : φ (τ₁ (γ, 1) v) = τ₂ (γ, 1) (φ v) := φ.isIntertwining _ _ _ _
  show φ (τ₁ (γ, 1) v - (ψ γ : ℂ) • v) = τ₂ (γ, 1) (φ v) - (ψ γ : ℂ) • φ v
  rw [map_sub, e, map_smul]

def coinvMap (φ : τ₁.IntertwiningMap τ₂) (ψ : Γ →* ℂˣ) :
    (coinv τ₁ ψ).IntertwiningMap (coinv τ₂ ψ) where
  toLinearMap := Submodule.mapQ _ _ φ.toLinearMap (twRel_le_comap φ ψ)
  isIntertwining' := fun g => by
    refine Submodule.linearMap_qext _ ?_
    ext v
    exact congrArg (Submodule.Quotient.mk (p := twRel (τ₂.comp (MonoidHom.inl Γ G)) ψ))
      (φ.isIntertwining _ _ (1, g) v)

theorem coinvMap_mk (φ : τ₁.IntertwiningMap τ₂) (ψ : Γ →* ℂˣ) (v : V₁) :
    coinvMap φ ψ (Submodule.Quotient.mk v) = Submodule.Quotient.mk (φ v) := rfl

theorem twRel_le_map (φ : τ₁.IntertwiningMap τ₂) (hφ : Function.Surjective φ) (ψ : Γ →* ℂˣ) :
    twRel (τ₂.comp (MonoidHom.inl Γ G)) ψ ≤
      (twRel (τ₁.comp (MonoidHom.inl Γ G)) ψ).map φ.toLinearMap := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨γ, u, rfl⟩
  obtain ⟨v, rfl⟩ := hφ u
  refine ⟨τ₁ (γ, 1) v - (ψ γ : ℂ) • v, Submodule.subset_span ⟨γ, v, rfl⟩, ?_⟩
  have e : φ (τ₁ (γ, 1) v) = τ₂ (γ, 1) (φ v) := φ.isIntertwining _ _ _ _
  show φ (τ₁ (γ, 1) v - (ψ γ : ℂ) • v) = τ₂ (γ, 1) (φ v) - (ψ γ : ℂ) • φ v
  rw [map_sub, e, map_smul]

theorem coinvMap_surjective (φ : τ₁.IntertwiningMap τ₂) (hφ : Function.Surjective φ) (ψ : Γ →* ℂˣ) :
    Function.Surjective (coinvMap φ ψ) := by
  intro y
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  obtain ⟨v, rfl⟩ := hφ u
  exact ⟨Submodule.Quotient.mk v, rfl⟩

end Coinv

theorem coinvMap_exact {Γ G W V U : Type} [Group Γ] [Group G] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U]
    {τW : Representation ℂ (Γ × G) W} {τ : Representation ℂ (Γ × G) V}
    {τU : Representation ℂ (Γ × G) U} (i : τW.IntertwiningMap τ) (f : τ.IntertwiningMap τU)
    (hf : Function.Surjective f) (hif : Function.Exact i f) (ψ : Γ →* ℂˣ) :
    Function.Exact (coinvMap i ψ) (coinvMap f ψ) := by
  intro x
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  constructor
  · intro h
    have hv : f v ∈ twRel (τU.comp (MonoidHom.inl Γ G)) ψ :=
      (Submodule.Quotient.mk_eq_zero _).1 h
    obtain ⟨r, hr, hrv⟩ := twRel_le_map f hf ψ hv
    have hrv' : f r = f v := hrv
    have hz : f (v - r) = 0 := by rw [map_sub, hrv', sub_self]
    obtain ⟨w, hw⟩ := (hif (v - r)).1 hz
    refine ⟨Submodule.Quotient.mk w, ?_⟩
    rw [coinvMap_mk, hw]
    exact (Submodule.Quotient.eq _).2 (by simpa using (Submodule.neg_mem _ hr))
  · rintro ⟨y, hy⟩
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    have h0 : f (i w) = 0 := (hif (i w)).2 ⟨w, rfl⟩
    rw [← hy, coinvMap_mk, coinvMap_mk, h0]
    rfl

theorem main : ∀ (Γ G W V U : Type) [Group Γ] [Group G] [AddCommGroup W] [Module ℂ W] [AddCommGroup V] [Module ℂ V] [AddCommGroup U] [Module ℂ U] (τW : Representation ℂ (Γ × G) W) (τ : Representation ℂ (Γ × G) V) (τU : Representation ℂ (Γ × G) U) (i : τW.IntertwiningMap τ) (f : τ.IntertwiningMap τU), Function.Surjective f → Function.Exact i f → ∀ ψ : Γ →* ℂˣ, HasFiniteLength (coinv τW ψ) → HasFiniteLength (coinv τU ψ) → HasFiniteLength (coinv τ ψ) := by
  intro Γ G W V U _ _ _ _ _ _ _ _ τW τ τU i f hf hif ψ hW hU
  exact hasFiniteLength_of_exact _ _ _ (coinvMap i ψ) (coinvMap f ψ)
    (coinvMap_surjective f hf ψ) (coinvMap_exact i f hf hif ψ) hW hU

end GlobalTheory.CompanionTheory.CoinvExact
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GaloisCohomologyLocalGlobalDual
section
noncomputable section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.S2pt

namespace GlobalTheory.CompanionTheory.Galois.PlacesOfS

theorem localFinite_at_places : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (S : Finset (HeightOneSpectrum (𝓞 F))) (Av : S → ValuationSubring Ω) (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ) (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M) (hρ : ContAction ρ), LocalFiniteness → 0 < r → (∀ v : S, IsPlaceOver (Av v) v.1) → ∀ v : S, Finite (H0 (ρ.comp (locFam S Av v))) ∧ Finite (H1 (ρ.comp (locFam S Av v))) ∧ Finite (H2 (ρ.comp (locFam S Av v))) := by
  intro F Ω _ _ _ _ _ l _ r M _ _ _ _ _ S Av μ ρ hρ hF hr hA v
  obtain ⟨h0, h1, h2, -⟩ := hF F Ω l r M (Av v) (ρ.comp (locFam S Av v)) v.1 hr (hA v)
    (hρ.comp' (continuous_locFam S Av v))
  exact ⟨h0, h1, h2⟩

end GlobalTheory.CompanionTheory.Galois.PlacesOfS
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalEulerPlaces
section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.S2pt

namespace GlobalTheory.CompanionTheory.Gal

theorem localEuler_places : ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (r : ℕ) (M : Type) [AddCommGroup M] [Module (ZMod (l ^ r)) M] [Finite M] [TopologicalSpace M] [DiscreteTopology M] (S : Finset (HeightOneSpectrum (𝓞 F))) (Av : S → ValuationSubring Ω) (μ : GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* (ZMod (l ^ r))ˣ) (ρ : Representation (ZMod (l ^ r)) (GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M) (hρ : ContAction ρ), LocalEulerChar → 0 < r → (∀ v : S, IsPlaceOver (Av v) v.1) → ∀ v : S, (((l : ℕ) : 𝓞 F) ∈ v.1.asIdeal → Nat.card (H1 (ρ.comp (locFam S Av v))) = Nat.card (H0 (ρ.comp (locFam S Av v))) * Nat.card (H2 (ρ.comp (locFam S Av v))) * Nat.card M ^ locDeg v.1) ∧ (((l : ℕ) : 𝓞 F) ∉ v.1.asIdeal → Nat.card (H1 (ρ.comp (locFam S Av v))) = Nat.card (H0 (ρ.comp (locFam S Av v))) * Nat.card (H2 (ρ.comp (locFam S Av v)))) := by
  intro F Ω _ _ _ _ _ l _ r M _ _ _ _ _ S Av μ ρ hρ hE hr hA v
  exact hE F Ω l r M (Av v) (ρ.comp (locFam S Av v)) v.1 hr (hA v) (hρ.comp' (continuous_locFam S Av v))

end GlobalTheory.CompanionTheory.Gal
end

