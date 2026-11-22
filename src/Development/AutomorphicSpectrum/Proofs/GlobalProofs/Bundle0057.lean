import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsEqOfNatCastMulMem
import GroundTheory.GlobalFields.ComplexMultiplication.MainTheorem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0568
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0562
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0570
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0584
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0556
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0591
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0564
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0576
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0056
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1281
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0177
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0048
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1334
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0407
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0054
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0051
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DifferentiableAtOrbit

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.EllipticMainTheoremCM
section
open NumberField
open scoped nonZeroDivisors GlobalTheory.Idele

namespace GlobalTheory.CompanionTheory.Hypotheses₂

theorem ellipticMainTheoremCM : GlobalTheory.Published.EllipticMainTheoremCM := by
  classical
  intro K _ _ _ _ h2 Art hArt σ s hs X _ 𝔞 h𝔞 ξ hξ
  obtain ⟨Art₀, hArt₀, hlink⟩ := GlobalTheory.CompanionTheory.EllipticCM.exists_globalArtinMap_tied K h2
  have hEq : Art = Art₀ := MonoidHom.ext fun c =>
    GlobalTheory.CompanionTheory.GaloisAb.abelianization_eq_of_forall_abRestrict_eq K _ _ fun L h =>
      GlobalTheory.T.artin_map_abelian_unique K Art Art₀ hArt hArt₀ L h c
  subst hEq
  have hfound := hlink σ s hs
  let 𝔞u : (FractionalIdeal (𝓞 K)⁰ K)ˣ := Units.mk0 𝔞 h𝔞
  have hf := GlobalTheory.CompanionTheory.EllipticCM.isAnalyticUniformization_of_isAnalyticIso h2 X 𝔞 h𝔞 ξ hξ
  obtain ⟨f', ⟨hf', hrel⟩, -⟩ :=
    GroundTheory.Global.Elliptic.main_theorem_complexMultiplication h2 σ s hfound 𝔞u hf
  have hid : ((s⁻¹ • 𝔞u : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
      (GlobalTheory.EllipticCM.finitePart (K := K) s)⁻¹ • 𝔞 :=
    GlobalTheory.CompanionTheory.EllipticCM.inv_smul_eq_finitePart_inv_smul s 𝔞u
  rw [hid] at hf'
  have hex := GlobalTheory.CompanionTheory.EllipticUniformization.exists_analyticIso_of_isAnalyticUniformization _ _ f' hf'
  rw [GlobalTheory.CompanionTheory.EllipticDict.idealLattice_toAddSubgroup_eq_idealSub] at hex
  obtain ⟨ξ', hξ', hξf⟩ := hex
  refine GlobalTheory.EllipticCM.transports_of_exists h𝔞 rfl hξ' fun x => ?_
  obtain ⟨t, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _
    (GlobalTheory.Idele.mulEquiv (GlobalTheory.EllipticCM.finitePart (K := K) s)⁻¹ h𝔞 rfl (Submodule.Quotient.mk t))
  rw [← hy]
  have hq := (GlobalTheory.CompanionTheory.IdeleQuot.smulQuotient_inv_mk_eq_mk_iff_mulEquiv s 𝔞u t y).2 hy.symm
  have h3 := hrel t y hq
  rw [GlobalTheory.CompanionTheory.ConjPointDict.mapPoint_eq_pointMapRing, GlobalTheory.EllipticCM.torsionIncl_mk,
    GlobalTheory.EllipticCM.torsionIncl_mk, hξf, h3]
  rfl

end GlobalTheory.CompanionTheory.Hypotheses₂
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.HolomorphicLocalSectionsCompatibleStatement
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Set
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_local_sections_compatible : ∀ (X : Scheme.{0}) (s : X ⟶ Sp ℂ) (D : ℕ), IsProper s → SmoothOfRelativeDimension D s → ∀ (L : LB X), L.IsLB → ∀ h : L.ι → (Sp ℂ ⟶ X) → ℂ, (∀ (i : L.ι) (m : ℕ) (B : Set (Fin m → ℂ)) (y : (Fin m → ℂ) → (Sp ℂ ⟶ X)), IsOpen B → IsHolTo B y → (∀ b ∈ B, y b ≫ s = 𝟙 _ ∧ ⊤ ≤ y b ⁻¹ᵁ L.U i) → DifferentiableOn ℂ (fun b => h i (y b)) B) → (∀ (i j : L.ι) (x : Sp ℂ ⟶ X), x ≫ s = 𝟙 _ → ⊤ ≤ x ⁻¹ᵁ (L.U i ⊓ L.U j) → h i x = valAt' x (L.U i ⊓ L.U j) (L.g i j).val * h j x) → ∃ σ : L.Sec, ∀ (i : L.ι) (x : Sp ℂ ⟶ X), x ≫ s = 𝟙 _ → ⊤ ≤ x ⁻¹ᵁ L.U i → valAt' x (L.U i) (σ.f i) = h i x := by
  first | exact @GlobalTheory.CompanionTheory.Gaga.gagaSections_pure | exact GlobalTheory.CompanionTheory.Gaga.gagaSections_pure | (intros; apply GlobalTheory.CompanionTheory.Gaga.gagaSections_pure <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsSubquotientCompMulSingle
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.TD

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.Published GlobalTheory.LocGL.SupportUnique GlobalTheory.SplitRead GlobalTheory.JHMult
open GlobalTheory.DiagCell

set_option synthInstance.maxHeartbeats 400000

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V W Y : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup Y] [Module ℂ Y]

theorem cell_diag {α : Type} [Fintype α] [LinearOrder α] {m : α → Type} [∀ i, Fintype (m i)]
    [∀ i, DecidableEq (m i)] (b : SizeMatrix m m) (hrz : ∀ i j, j ≠ i → b.1 i j = 0)
    (ρ : Representation ℂ (Levi k m) W) (hsm : IsSmooth ρ) :
    ∃ (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ m i) (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ m j),
      Nonempty ((cellFunctor f g ρ).Equiv ρ) := by
  have hcz : ∀ j i, i ≠ j → b.1 i j = 0 := fun j i hi => hrz i j (Ne.symm hi)
  have hcard : ∀ i, Fintype.card (Fin (b.1 i i)) = Fintype.card (m i) := by
    intro i
    have r := b.2.1 i
    rw [Finset.sum_eq_single i (fun j _ hj => hrz i j hj) (by simp)] at r
    simpa using r
  let E : ∀ i, Fin (b.1 i i) ≃ m i := fun i => Fintype.equivOfCardEq (hcard i)
  let f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ m i := fun i =>
    (OneBlockCell.valEquiv (n := fun j => b.1 i j) i rfl (fun j hj => hrz i j hj)).trans (E i)
  let g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ m j := fun j =>
    (OneBlockCell.valEquiv (n := fun i => b.1 i j) j rfl (fun i hi => hcz j i hi)).trans (E j)
  refine ⟨f, g, ?_⟩
  have hbot : twKer ρ (relUnip k f) 1 = ⊥ := by
    refine eq_bot_iff.2 (Submodule.span_le.2 ?_)
    rintro _ ⟨n, v, rfl⟩
    have : (n : Levi k m) = 1 := funext fun i =>
      eq_one_of_mem_unipRad_single (f i) i (fun j hj => hrz i j hj) (n.2 i trivial)
    simp [this]
  have hδ : ∀ z, relDeltaHalf k (fun i j => Fin (b.1 i j)) z = 1 := fun z => by
    rw [relDeltaHalf_apply]
    exact Finset.prod_eq_one fun i _ =>
      OneBlockCell.deltaHalf_eq_one_of_single i (fun j hj => hrz i j hj) (z i)
  have hδ' : ∀ z, relDeltaHalf k (fun j i => Fin (b.1 i j)) z = 1 := fun z => by
    rw [relDeltaHalf_apply]
    exact Finset.prod_eq_one fun j _ =>
      OneBlockCell.deltaHalf_eq_one_of_single j (fun i hi => hcz j i hi) (z j)
  have hP : ∀ x, x ∈ relParab k g := fun x j _ =>
    mem_parab_of_single (g j) j (fun i hi => hcz j i hi) (x j)
  have hfg : ∀ i (t : Fin (b.1 i i)), f i ⟨i, t⟩ = g i ⟨i, t⟩ := fun i t => rfl
  have hγ : ∀ (p : relParab k g),
      relEmb k f (swapBlocks k (fun i j => Fin (b.1 i j)) (relProj k g p)) =
        (p : Levi k m) := by
    intro p
    funext i
    rw [relEmb_apply]
    refine Units.ext (Matrix.ext fun x y => ?_)
    obtain ⟨⟨a, t⟩, rfl⟩ := (f i).surjective x
    obtain ⟨⟨a', s⟩, rfl⟩ := (f i).surjective y
    have ha : a = i := by
      by_contra hne
      have h1 := hrz i a hne
      have h2 := t.2
      omega
    have ha' : a' = i := by
      by_contra hne
      have h1 := hrz i a' hne
      have h2 := s.2
      omega
    subst ha
    subst ha'
    rw [leviEmb_apply_same, hfg, hfg]
    rfl
  let Ψ : W ≃ₗ[ℂ] Jacquet ρ (relUnip k f) := (Submodule.quotEquivOfEqBot _ hbot).symm
  have hΨ : ∀ u, Ψ u = Submodule.Quotient.mk u := fun u => rfl
  let τ := (twist ((relJac f ρ).comp (swapBlocks k (fun i j => Fin (b.1 i j))))
        (relDeltaHalf k (fun j i => Fin (b.1 i j)))).comp (relProj k g)
  have law : ∀ (p : relParab k g) u, τ p (Ψ u) = Ψ (ρ p u) := by
    intro p u
    rw [MonoidHom.comp_apply, twist_apply, MonoidHom.comp_apply, hΨ, relJac_mk, hδ, hδ', hΨ, hγ p]
    simp only [inv_one, Units.val_one, one_smul]
  let F : ρ.IntertwiningMap (cellFunctor f g ρ) :=
    { toFun := fun u => ⟨⟨fun x => Ψ (ρ x u), fun p x => by
          show Ψ (ρ (↑p * x) u) = _
          rw [map_mul, Module.End.mul_apply]
          exact (law p _).symm⟩,
        mem_smoothPart_of_nhds (Filter.mem_of_superset ((hsm u).mem_nhds (by simp)) fun x hx => by
          have hx' : ρ x u = u := hx
          refine Subtype.ext (funext fun y => ?_)
          show Ψ (ρ (y * x) u) = Ψ (ρ y u)
          rw [map_mul, Module.End.mul_apply, hx'])⟩
      map_add' := fun u w => Subtype.ext (Subtype.ext (funext fun x => by simp))
      map_smul' := fun c u => Subtype.ext (Subtype.ext (funext fun x => by simp))
      isIntertwining' := fun h => LinearMap.ext fun u => Subtype.ext (Subtype.ext (funext fun x => by
        show Ψ (ρ x (ρ h u)) = Ψ (ρ (x * h) u)
        rw [map_mul, Module.End.mul_apply])) }
  refine ⟨(LocGL.equivOfBijective F ⟨fun u w hw => ?_, fun φ => ⟨Ψ.symm (φ.1.1 1),
    Subtype.ext (Subtype.ext (funext fun x => ?_))⟩⟩).symm⟩
  · have h1 : Ψ (ρ 1 u) = Ψ (ρ 1 w) := congrArg (fun φ => φ.1.1 1) hw
    simpa using h1
  · show Ψ (ρ x (Ψ.symm (φ.1.1 1))) = φ.1.1 x
    refine (law ⟨x, hP x⟩ (Ψ.symm (φ.1.1 1))).symm.trans ?_
    refine (congrArg (τ ⟨x, hP x⟩) (Ψ.apply_symm_apply (φ.1.1 1))).trans ?_
    refine (φ.1.2 ⟨x, hP x⟩ 1).symm.trans ?_
    exact congrArg φ.1.1 (mul_one x)

theorem isSubquotient_comp_mulSingle {α : Type} [Fintype α] [DecidableEq α] {Γ X : α → Type} [∀ a, Group (Γ a)]
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (Γ a) (X a))
    (hi : ∀ a, (ρ a).IsIrreducible) (c : α) :
    IsSubquotient (ρ c) ((piTensor ρ).comp (MonoidHom.mulSingle Γ c) :
      Representation ℂ (Γ c) (PiTensorProduct ℂ fun a => X a)) := by
  have hn := GlobalTheory.ProdSupport.nontrivial_piTensor X fun a => GlobalTheory.SmGL.Model.nontrivial_of_isIrreducible (hi a)
  obtain ⟨Z, _, _, υ, hυ, hs⟩ := GlobalTheory.IrrSubquot.exists_irreducible_subquotient _ _
    ((piTensor ρ).comp (MonoidHom.mulSingle Γ c)) hn
  obtain ⟨φ⟩ := nonempty_equiv_of_isSubquotient hυ (hi c) (isSubquotient_factor ρ c hυ hs)
  exact (IsSubquotient.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective).trans hs

theorem exists_of_cell (h' : CellSemisimplification k) {α β : Type} [Fintype α] [LinearOrder α] [Fintype β]
    [LinearOrder β] {m : α → Type} [∀ i, Fintype (m i)] [∀ i, DecidableEq (m i)] {m' : β → Type}
    [∀ j, Fintype (m' j)] [∀ j, DecidableEq (m' j)] {b : α → β → ℕ}
    (f : ∀ i, (Σ j, Fin (b i j)) ≃ m i) (g : ∀ j, (Σ i, Fin (b i j)) ≃ m' j)
    {X : α → Type} [∀ i, AddCommGroup (X i)] [∀ i, Module ℂ (X i)]
    {ρ : ∀ i, Representation ℂ (GL (m i) k) (X i)} (hρ : ∀ i, IsSmooth (ρ i)) (hl : ∀ i, HasFiniteLength (ρ i))
    {τ : Representation ℂ (Levi k m') Y} (hτ : τ.IsIrreducible) (hτs : IsSmooth τ)
    (h0 : jhMult τ (cellFunctor f g (piTensor ρ)) ≠ 0) :
    ∃ s : ∀ i j, IrrRep (GL (Fin (b i j)) k),
      (∀ i, IsSubquotient (piTensor fun j => (s i j).ρ) (jac (f i) (ρ i))) ∧
        IsSubquotient τ (piTensor fun j => multiProd (g j) fun i => (s i j).ρ) := by
  obtain ⟨T, -, hT⟩ := h' α β m m' _ f g X ρ hρ hl
  rw [hT ⟨Y, τ, hτs, hτ⟩] at h0
  obtain ⟨s, -, hs⟩ := Finset.exists_ne_zero_of_sum_ne_zero h0
  exact ⟨fun i j => (s i j).rep, fun i => jhMult_ne_zero_iff.1
    (Finset.prod_ne_zero_iff.1 (left_ne_zero_of_mul hs) i (Finset.mem_univ i)),
    jhMult_ne_zero_iff.1 (right_ne_zero_of_mul hs)⟩

theorem offdiag_eq_zero (hG : GeometricLemma) (hBZ : BernsteinZelevinskyFiniteness) {d : Fin 2 → ℕ}
    (p : ∀ i, Irr k (d i)) {A : Fin 2 → Multiset (IrrGL k)} (hA : ∀ i, HasSupport (p i).π (A i))
    (hAB : ∀ x ∈ A 0, x ∉ A 1) {b : Fin 2 → Fin 2 → ℕ}
    (f : ∀ i, (Σ j, Fin (b i j)) ≃ Fin (d i)) (g : ∀ j, (Σ i, Fin (b i j)) ≃ Fin (d j))
    {τ : Representation ℂ (Levi k fun i => Fin (d i)) Y} (hτ : τ.IsIrreducible) (hτs : IsSmooth τ)
    (y : ∀ i, IrrRep (GL (Fin (d i)) k))
    (hy : ∀ i, IsSubquotient (y i).ρ (τ.comp (MonoidHom.mulSingle (fun i => GL (Fin (d i)) k) i) :
      Representation ℂ (GL (Fin (d i)) k) Y))
    (hys : ∀ i, HasSupport (y i).ρ (A i))
    (h0 : jhMult τ (cellFunctor f g (piTensor fun i => (p i).π)) ≠ 0) : b 0 1 = 0 ∧ b 1 0 = 0 := by
  obtain ⟨s, hrow, hcol⟩ := exists_of_cell (hG k).2 f g (fun i => (p i).smooth)
    (fun i => hasFiniteLength_of_isIrreducible (p i).irr) hτ hτs h0
  have hR : ∀ i, ∃ t : Fin 2 → Multiset (IrrGL k), (∀ j, HasSupport (s i j).ρ (t j)) ∧ A i = ∑ j, t j :=
    fun i => exists_sum_of_jac hG hBZ (hA i) (f i) (GlobalTheory.T.piExteriorTensor_smoothIrreducible_isIrreducible hBZ k _ _ fun j => s i j) (hrow i)
      (fun j => s i j) (fun j => isSubquotient_comp_mulSingle _ (fun j => (s i j).irr) j)
  choose t ht hAt using hR
  have hC : ∀ j, HasSupport (y j).ρ (∑ i, t i j) := by
    intro j
    have hd : ∑ i, b i j = d j := by simpa using Fintype.card_congr (g j)
    have h1 := isSubquotient_factor (fun j => multiProd (g j) fun i => (s i j).ρ) j (y j).irr
      ((hy j).trans (isSubquotient_comp hcol _))
    obtain ⟨φ⟩ := (GlobalTheory.SmGL.Placing.parInd_jac_placing k _ _ _ (g j) (stdBlocks (fun i => b i j) hd) _).1
      (piTensor fun i => (s i j).ρ)
    let ψ := φ.trans (prodIrrEquiv hd (fun i => (s i j).ρ) (fun i => (s i j).smooth) fun i => (s i j).irr)
    exact hasSupport_of_isSubquotient_prodIrr
      (y := fun i => IrrGL.of (s i j).ρ (s i j).smooth (s i j).irr)
      (fun i => (ht i j).of_equiv (IrrGL.equivOf _ _ _)) (y j).irr
      (h1.trans (.of_injective ψ.toIntertwiningMap ψ.toLinearEquiv.injective))
  have hU : ∀ j, A j = ∑ i, t i j := fun j => hasSupport_unique hG hBZ (hys j) (hC j)
  simp only [Fin.sum_univ_two] at hAt hU
  have e1 : t 0 1 = t 1 0 := add_left_cancel ((hAt 0).symm.trans (hU 0))
  have hw : t 0 1 = 0 := Multiset.eq_zero_of_forall_notMem fun x hx =>
    hAB x (hAt 0 ▸ Multiset.mem_add.2 (Or.inr hx)) (hAt 1 ▸ Multiset.mem_add.2 (Or.inl (e1 ▸ hx)))
  have hd1 := (ht 0 1).sum_fst
  have hd2 := (ht 1 0).sum_fst
  rw [← e1, hw] at hd2
  rw [hw] at hd1
  simp only [Multiset.map_zero, Multiset.sum_zero, Fintype.card_fin] at hd1 hd2
  exact ⟨hd1.symm, hd2.symm⟩

theorem jhMult_jac_multiProd (hG : GeometricLemma) (hBZ : BernsteinZelevinskyFiniteness) {d : Fin 2 → ℕ}
    (p : ∀ i, Irr k (d i)) {A : Fin 2 → Multiset (IrrGL k)} (hA : ∀ i, HasSupport (p i).π (A i))
    (hAB : ∀ x ∈ A 0, x ∉ A 1) {N : ℕ} (e e' : (Σ i, Fin (d i)) ≃ Fin N)
    {τ : Representation ℂ (Levi k fun i => Fin (d i)) Y} (hτ : τ.IsIrreducible) (hτs : IsSmooth τ)
    (y : ∀ i, IrrRep (GL (Fin (d i)) k))
    (hy : ∀ i, IsSubquotient (y i).ρ (τ.comp (MonoidHom.mulSingle (fun i => GL (Fin (d i)) k) i) :
      Representation ℂ (GL (Fin (d i)) k) Y))
    (hys : ∀ i, HasSupport (y i).ρ (A i)) :
    jhMult τ (jac e' (multiProd e fun i => (p i).π)) = jhMult τ (piTensor fun i => (p i).π) := by
  classical
  let M := fun i : Fin 2 => Fin (d i)
  haveI : Fintype (SizeMatrix M M) := Fintype.ofFinite _
  let b₀ : SizeMatrix M M := ⟨fun i j => if i = j then d i else 0, by
    refine ⟨fun i => ?_, fun j => ?_⟩
    · simp [M]
    · simp [M]⟩
  have hρ : IsSmooth (piTensor fun i => (p i).π) := isSmooth_piTensor fun i => (p i).smooth
  obtain ⟨f₀, g₀, ⟨E₀⟩⟩ := cell_diag b₀ (fun i j hj => by simp [b₀, Ne.symm hj]) _ hρ
  let f : ∀ (b : SizeMatrix M M) i, (Σ j, Fin (b.1 i j)) ≃ M i := fun b =>
    if h : b = b₀ then h ▸ f₀ else b.nonempty_rows.some
  let g : ∀ (b : SizeMatrix M M) j, (Σ i, Fin (b.1 i j)) ≃ M j := fun b =>
    if h : b = b₀ then h ▸ g₀ else b.nonempty_cols.some
  have hf : f b₀ = f₀ := by simp [f]
  have hg : g b₀ = g₀ := by simp [g]
  have h1 := (hG k).1.jhMult_eq (m := M) (m' := M) e e' hρ f g hτ
  refine (show jhMult τ (jac e' (multiProd e fun i => (p i).π)) = _ from h1).trans ?_
  rw [Finset.sum_eq_single b₀]
  · have key : ∀ (f' : ∀ i, (Σ j, Fin (b₀.1 i j)) ≃ M i) (g' : ∀ j, (Σ i, Fin (b₀.1 i j)) ≃ M j), f' = f₀ → g' = g₀ →
        jhMult τ (cellFunctor f' g' (piTensor fun i => (p i).π)) = jhMult τ (piTensor fun i => (p i).π) := by
      rintro _ _ rfl rfl
      exact jhMult_congr_right τ E₀
    exact key _ _ hf hg
  · intro b _ hb
    by_contra hne
    obtain ⟨z1, z2⟩ := offdiag_eq_zero hG hBZ p hA hAB (f b) (g b) hτ hτs y hy hys hne
    refine hb (Subtype.ext (funext fun i => funext fun j => ?_))
    have r0 := b.2.1 0
    have r1 := b.2.1 1
    simp only [Fin.sum_univ_two, M, Fintype.card_fin] at r0 r1
    fin_cases i <;> fin_cases j <;> simp_all [b₀]
  · simp

end GlobalTheory.CompanionTheory.Hypotheses₂.TD
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.IterateRealSmul
section
noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA.OneParam

variable {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem mnorm_real_smul (s : ℝ) (X : Matrix (Fin n) (Fin n) ℂ) : mnorm (s • X) = |s| * mnorm X := by
  unfold mnorm
  simp only [Matrix.smul_apply, norm_smul, Real.norm_eq_abs, Finset.mul_sum]

theorem mnorm_nonneg (X : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ mnorm X :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem iterate_smooth (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {v : H} (hs : IsSmoothVec G π v)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) (m : ℕ) :
    IsSmoothVec G π ((dRep π X)^[m] v) := by
  induction m with
  | zero => simpa using hs
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    exact (GlobalTheory.T.derived_action_of_smooth_vector hG hrep ih hX).2

theorem iterate_real_smul (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {v : H} (hs : IsSmoothVec G π v)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) (s : ℝ) (m : ℕ) :
    (dRep π (s • X))^[m] v = ((s : ℂ) ^ m) • (dRep π X)^[m] v := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hsm := iterate_smooth hG hrep hs hX m
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply', GlobalTheory.GKLie.dRep_smul,
      (GlobalTheory.T.derived_action_additive hG hrep hsm hsm hX hX).2.2, ← Complex.coe_smul, smul_smul, pow_succ']

theorem analytic_coeff : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G)
    (hU : IsURepOn G π) {v : H} (hs : IsSmoothVec G π v) (hw : WordBound G π v)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G) (w : H),
    AnalyticOnNhd ℝ (fun t : ℝ => ⟪w, π (NormedSpace.exp (t • X)) v⟫_ℂ) Set.univ := by
  intro n G H _ _ _ π hG hU v hs hw X hX w t₀ _
  obtain ⟨r, hr, hsum⟩ := GlobalTheory.T.analytic_vector_exponential_series hG hU.1 hU.2.2 hs hw
  have hrep := hU.1
  let L : H →L[ℂ] ℂ := (innerSL ℂ w).comp (π (NormedSpace.exp (t₀ • X)))
  let a : ℕ → ℂ := fun m => ((m.factorial : ℂ)⁻¹) * L ((dRep π X)^[m] v)
  have key : ∀ s : ℝ, |s| * mnorm X < r → HasSum (fun m : ℕ => (s : ℂ) ^ m * a m)
      (⟪w, π (NormedSpace.exp ((t₀ + s) • X)) v⟫_ℂ) := by
    intro s hs'
    have h1 := hsum (s • X) ((GlobalTheory.T.lie_algebra_of_linear_group_closed hG).2.1 s X hX) (by rwa [mnorm_real_smul])
    have h2 := L.hasSum h1
    have e : ⟪w, π (NormedSpace.exp ((t₀ + s) • X)) v⟫_ℂ = L (π (NormedSpace.exp (s • X)) v) := by
      have hc : Commute (t₀ • X) (s • X) := ((Commute.refl X).smul_left t₀).smul_right s
      rw [add_smul, Matrix.exp_add_of_commute _ _ hc, hrep.2 _ (hX t₀) _ (hX s)]
      rfl
    rw [e]
    convert h2 using 2 with m
    rw [iterate_real_smul hG hrep hs hX s m]
    simp only [a, map_smul, smul_eq_mul]
    ring
  let p : FormalMultilinearSeries ℝ ℝ ℂ := fun m => ContinuousMultilinearMap.mkPiRing ℝ (Fin m) (a m)
  have hpa : ∀ (m : ℕ) (s : ℝ), p m (fun _ => s) = (s : ℂ) ^ m * a m := by
    intro m s
    simp [p, ContinuousMultilinearMap.mkPiRing_apply]
  have hM : 0 < mnorm X + 1 := by linarith [mnorm_nonneg X]
  have hsmall : ∀ s : ℝ, |s| < r / (mnorm X + 1) → |s| * mnorm X < r := by
    intro s h
    rw [lt_div_iff₀ hM] at h
    nlinarith [abs_nonneg s]
  set ε : ℝ := r / (mnorm X + 1) with hε
  have hεpos : 0 < ε := div_pos hr hM
  have hrad : 0 < p.radius := by
    have hs0 : |ε / 2| < ε := by rw [abs_of_pos (by linarith)]; linarith
    have hS := (key (ε / 2) (hsmall _ hs0)).summable.norm
    let ρ : NNReal := ⟨ε / 2, by linarith⟩
    have hρ : (0 : NNReal) < ρ := by
      change (0 : ℝ) < ε / 2
      linarith
    have : (ρ : ENNReal) ≤ p.radius := by
      refine p.le_radius_of_summable_norm ?_
      refine hS.congr fun m => ?_
      have hρc : ((ρ : NNReal) : ℝ) = ε / 2 := rfl
      simp [p, hρc, ContinuousMultilinearMap.norm_mkPiRing, abs_of_pos hεpos, mul_comm]
    exact lt_of_lt_of_le (by exact_mod_cast hρ) this
  have han : AnalyticAt ℝ p.sum 0 := (p.hasFPowerSeriesOnBall hrad).analyticAt
  have han2 : AnalyticAt ℝ (fun t : ℝ => p.sum (t - t₀)) t₀ :=
    AnalyticAt.comp_of_eq (g := p.sum) (f := fun t : ℝ => t - t₀) han
      (analyticAt_id.sub analyticAt_const) (by simp)
  refine han2.congr ?_
  filter_upwards [Metric.ball_mem_nhds t₀ hεpos] with t ht
  have hd : |t - t₀| < ε := by simpa [Real.dist_eq] using ht
  have h3 := key (t - t₀) (hsmall _ hd)
  rw [show t₀ + (t - t₀) = t by ring] at h3
  simp only [FormalMultilinearSeries.sum, hpa]
  exact h3.tsum_eq

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA.OneParam

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.LieBasisCoordinateGrowthBoundStatement
section
open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_basis_coordinate_growth_bound : ∀ {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G) (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {d : ℕ} (b : Fin d → Matrix (Fin n) (Fin n) ℂ) (hb : ∀ i, b i ∈ HCSS.lieOf G) (hsp : ∀ X ∈ HCSS.lieOf G, ∃ r : Fin d → ℝ, X = ∑ i, r i • b i) (D : ℝ) (hD0 : 0 ≤ D) (hD : ∀ r : Fin d → ℝ, ∑ i, |r i| ≤ D * mnorm (∑ i, r i • b i)) (hexp : ∀ (r : Fin d → ℝ) (w : H), IsSmoothVec G π w → dRep π (∑ i, r i • b i) w = ∑ i, (r i : ℂ) • dRep π (b i) w) {v : H} (hv : IsSmoothVec G π v) (C : ℝ) (hC : 0 < C) (hbound : ∀ l : List (Fin d), ‖l.foldr (fun i w => dRep π (b i) w) v‖ ≤ C ^ (l.length + 1) * l.length.factorial), WordBound G π v := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.HCA.WordExpand.wordBound_of_basis | exact GlobalTheory.CompanionTheory.Hypotheses₂.HCA.WordExpand.wordBound_of_basis | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.HCA.WordExpand.wordBound_of_basis <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GlobalProofs.SumSquaresComm
section
noncomputable section

open Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.LinRed GlobalTheory.FlagMeas GlobalTheory.RealInd GlobalTheory.CompanionTheory.Hypotheses₂ GlobalTheory.CompanionTheory.Hypotheses₂.HCA
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.CompanionTheory.Hypotheses₂.HCA

theorem dRep_realSum {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G)
    (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {u : H} (hu : IsSmoothVec G π u) {ι : Type} (s : Finset ι)
    (c : ι → ℝ) (a : ι → Matrix (Fin n) (Fin n) ℂ) (ha : ∀ l, a l ∈ HCSS.lieOf G)
    (h0 : (0 : Matrix (Fin n) (Fin n) ℂ) ∈ HCSS.lieOf G) :
    (∑ l ∈ s, c l • a l) ∈ HCSS.lieOf G ∧
      dRep π (∑ l ∈ s, c l • a l) u = ∑ l ∈ s, c l • dRep π (a l) u := by
  classical
  obtain ⟨hadd, hsm, -, -⟩ := GlobalTheory.T.lie_algebra_of_linear_group_closed hG
  induction s using Finset.induction_on with
  | empty => simpa using ⟨h0, GlobalTheory.GKLie.dRep_zero π u⟩
  | insert x s hx ih =>
    rw [Finset.sum_insert hx, Finset.sum_insert hx]
    have h1 := hsm (c x) _ (ha x)
    refine ⟨hadd _ _ h1 ih.1, ?_⟩
    rw [(GlobalTheory.T.derived_action_additive hG hrep hu hu h1 ih.1).1, ih.2, GlobalTheory.GKLie.dRep_smul]

theorem dRep_vecSum {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G)
    (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ HCSS.lieOf G)
    {ι : Type} (s : Finset ι) (c : ι → ℝ) (u : ι → H) (hu : ∀ l, IsSmoothVec G π (u l)) :
    IsSmoothVec G π (∑ l ∈ s, c l • u l) ∧
      dRep π X (∑ l ∈ s, c l • u l) = ∑ l ∈ s, c l • dRep π X (u l) := by
  classical
  obtain ⟨hadd, hsm, -⟩ := GlobalTheory.T.smooth_vectors_invariant_subspace hG hrep
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨?_, by simp [dRep]⟩
    exact ⟨fun _ => 0, contDiff_const, fun z _ => by simp⟩
  | insert x s hx ih =>
    rw [Finset.sum_insert hx, Finset.sum_insert hx]
    have h1 : IsSmoothVec G π (c x • u x) := by
      rw [← Complex.coe_smul]
      exact hsm _ _ (hu x)
    refine ⟨hadd _ _ h1 ih.1, ?_⟩
    rw [(GlobalTheory.T.derived_action_additive hG hrep h1 ih.1 hX hX).2.1, ih.2, ← Complex.coe_smul,
      (GlobalTheory.T.derived_action_additive hG hrep (hu x) (hu x) hX hX).2.2, Complex.coe_smul]

theorem sumSquares_comm {n : ℕ} {G : Set (Matrix (Fin n) (Fin n) ℂ)} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hG : IsLinRed G)
    (hrep : Formalism.QuantumDeterminants.IsCRepOn G π) {d : ℕ} (b : Fin d → Matrix (Fin n) (Fin n) ℂ)
    (hb : ∀ i, b i ∈ HCSS.lieOf G) {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ G)
    (O : Matrix (Fin d) (Fin d) ℝ) (hO : Oᵀ * O = 1) (hkb : ∀ i, k * b i * k⁻¹ = ∑ l, O l i • b l)
    {v : H} (hv : IsSmoothVec G π v) :
    π k (∑ i, dRep π (b i) (dRep π (b i) v)) = ∑ i, dRep π (b i) (dRep π (b i) (π k v)) := by
  rcases isEmpty_or_nonempty (Fin d) with hd | ⟨⟨i0⟩⟩
  · simp [Finset.univ_eq_empty]
  have h0 : (0 : Matrix (Fin n) (Fin n) ℂ) ∈ HCSS.lieOf G := by
    simpa using (GlobalTheory.T.lie_algebra_of_linear_group_closed hG).2.1 0 _ (hb i0)
  have hw : IsSmoothVec G π (π k v) := (GlobalTheory.T.smooth_vectors_invariant_subspace hG hrep).2.2 k hk v hv
  have hT : ∀ m, IsSmoothVec G π (dRep π (b m) (π k v)) := fun m =>
    (GlobalTheory.T.derived_action_of_smooth_vector hG hrep hw (hb m)).2
  have step : ∀ i, π k (dRep π (b i) (dRep π (b i) v)) =
      ∑ l, ∑ m, (O l i * O m i) • dRep π (b l) (dRep π (b m) (π k v)) := by
    intro i
    have hsm := (GlobalTheory.T.derived_action_of_smooth_vector hG hrep hv (hb i)).2
    rw [GlobalTheory.T.derived_action_conjugation hG hrep hsm (hb i) hk, GlobalTheory.T.derived_action_conjugation hG hrep hv (hb i) hk, hkb i,
      (dRep_realSum hG hrep hw Finset.univ (fun m => O m i) b hb h0).2,
      (dRep_realSum hG hrep
        (dRep_vecSum hG hrep (hb i0) Finset.univ (fun m => O m i) _ hT).1
        Finset.univ (fun l => O l i) b hb h0).2]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [(dRep_vecSum hG hrep (hb l) Finset.univ (fun m => O m i) _ hT).2, Finset.smul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [smul_smul]
  have hOO : O * Oᵀ = 1 := mul_eq_one_comm.1 hO
  have hdelta : ∀ l m, ∑ i, O l i * O m i = (1 : Matrix (Fin d) (Fin d) ℝ) l m := fun l m => by
    rw [← hOO]
    simp [Matrix.mul_apply]
  rw [map_sum, Finset.sum_congr rfl fun i _ => step i, Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, hdelta, Matrix.one_apply]
  simp

end GlobalTheory.CompanionTheory.Hypotheses₂.HCA

end
end

