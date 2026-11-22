import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0018
import Development.AutomorphicSpectrum.Definitions.NonGaloisLines.TopLine
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CoboundaryMemBlochKatoCocycles
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.Bundle0002
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.Bundle0004
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.Bundle0005
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.DualQOfTopInj
import Development.AutomorphicSpectrum.Proofs.NonGaloisProofs.GrowthGaloisInvariantsModPrimePowerLattice
import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.Bundle0001

-- bundled from Development.WeilBound.CoreStatements.EulerCharacteristicCounts.BkPair
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module GlobalTheory.CompanionTheory.LocDual

namespace PositivityTheory.LocalTateOrthogonality.Bk

set_option maxHeartbeats 2000000 in
theorem pairO : ∀ (D : D7) (l : ℕ) [Fact l.Prime] (K : FinExt l), ∀ (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A A' : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (LA' : Lattice (O := O) A'.ρ) (P : A.V →ₗ[LL] A'.V →ₗ[LL] LL), IsDualLat1 ((D.loc l).PD K) LA LA' P → ∀ ϖ : O, Irreducible ϖ → ∀ r : ℕ, ∃ B : (↥LA.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)) →ₗ[O] (↥LA'.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA'.T)) →ₗ[O] (O ⧸ Ideal.span {ϖ ^ r}), (∀ (x : ↥LA.T) (y : ↥LA'.T) (p : O), P x y = algebraMap O LL p → B (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) = Ideal.Quotient.mk _ p) ∧ (∀ x, (∀ y, B x y = 0) → x = 0) ∧ (∀ y, (∀ x, B x y = 0) → y = 0) := by
  intro D l _ K LL _ _ _ O _ _ hG A A' LA LA' P hd ϖ hϖ r
  have hG0 : ∃ hO : IsDomain O, @IsDiscreteValuationRing O _ hO ∧ IsFractionRing O LL := hG.1
  have hO : IsDomain O := hG0.choose
  have hF : IsFractionRing O LL := hG0.choose_spec.2
  have h1 : ∀ y, y ∈ LA'.T ↔ ∀ x ∈ LA.T, ∃ a : O, P x y = algebraMap O LL a := hd.2
  have h2 : ∀ x, x ∈ LA.T ↔ ∀ y ∈ LA'.T, ∃ a : O, P.flip y x = algebraMap O LL a :=
    ((GlobalTheory.T.lattice_open_compact_nhds_basis D l K LL O hG A LA ϖ hϖ).2.2.2.2 A' LA' P hd).2
  simp only [LinearMap.flip_apply] at h2
  exact GlobalTheory.CompanionTheory.LocDual.Q.pairing_exists LL O A.V A'.V LA.T LA'.T P ϖ hϖ.ne_zero r h1 h2

theorem cardQ : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l), ∀ (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (ϖ : O), Irreducible ϖ → ∀ r : ℕ, Finite (↥LA.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)) ∧ Nat.card (↥LA.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)) = Nat.card (O ⧸ Ideal.span {ϖ}) ^ (r * finrank LL A.V) := by
  intro l _ K LL _ _ _ O _ _ hG A LA ϖ hϖ r
  obtain ⟨⟨hO, hD, hF⟩, -⟩ := id hG
  have := hO
  have := hD
  have := hF
  have hq := (GlobalTheory.T.goodO_adic_complete_compact_basis l LL O hG ϖ hϖ).2.1
  refine ⟨(GlobalTheory.CompanionTheory.LocDual.Q.finite_quot O A.V LA.T ϖ r hq LA.fg).2, ?_⟩
  have : Module.Finite O ↥LA.T := Module.Finite.iff_fg.mpr LA.fg
  have := LA.free
  rw [GlobalTheory.CompanionTheory.GrowthOfInvariants.card_quot_free (Module.finBasis O ↥LA.T).equivFun,
    GlobalTheory.CompanionTheory.GrowthOfInvariants.card_quot_pow ϖ hϖ.ne_zero, GlobalTheory.H1fGeneratorBoundAlt.finrank_lattice LA, pow_mul]

theorem locconst : ∀ (_D : D7) (l : ℕ) [Fact l.Prime] (K : FinExt l), ∀ (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ) (ϖ : O), Irreducible ϖ → ∀ (r : ℕ) (hI : StableSub LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)) (m : ↥LA.T ⧸ (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)), IsLocallyConstant fun g => actQ LA _ hI g m := by
  intro D l _ K LL _ _ _ O _ _ hG A LA ϖ hϖ r hI m
  exact GlobalTheory.CompanionTheory.LocDual.Q.act_locConst D l K LL O hG A LA ϖ hϖ r hI m

end PositivityTheory.LocalTateOrthogonality.Bk
end

-- bundled from Development.WeilBound.CoreStatements.EulerCharacteristicCounts.ExistsDivClass
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module GlobalTheory.CompanionTheory.LocDual

namespace PositivityTheory.LocalTateOrthogonality.Bk

theorem card_pow_le {O M Z N : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [AddCommGroup M]
    [Module O M] [Module.Finite O M] [Finite N] (a : O) (p : Z → M) (hp : Function.Surjective p)
    (f : Z → N) (hf : ∀ x y, f x = f y → ∃ w, p x - p y = a • w) :
    Nat.card (O ⧸ Ideal.span {a}) ^ finrank O M ≤ Nat.card N := by
  classical
  set I : Ideal O := Ideal.span {a}
  let F := M ⧸ Submodule.torsion O M
  let b := Module.finBasis O F
  have e : finrank O F = finrank O M := finrank_quotient_eq_of_le_torsion le_rfl
  let ψL : M →ₗ[O] (Fin (finrank O F) → O) := b.equivFun.toLinearMap ∘ₗ (Submodule.torsion O M).mkQ
  let ψ : M → (Fin (finrank O F) → O ⧸ I) := fun m i => Ideal.Quotient.mk I (ψL m i)
  have hψ : ∀ x y, (∃ w, x - y = a • w) → ψ x = ψ y := by
    rintro x y ⟨w, hw⟩
    funext i
    refine Ideal.Quotient.eq.mpr ?_
    have h1 : ψL x i - ψL y i = a * ψL w i := by
      rw [← Pi.sub_apply, ← map_sub, hw, map_smul]
      rfl
    rw [h1]
    exact Ideal.mem_span_singleton'.mpr ⟨ψL w i, mul_comm _ _⟩
  have hsurj : Function.Surjective (fun z => ψ (p z)) := by
    intro t
    choose c hc using fun i => Ideal.Quotient.mk_surjective (I := I) (t i)
    obtain ⟨m, hm⟩ := (Submodule.torsion O M).mkQ_surjective (b.equivFun.symm c)
    obtain ⟨z, rfl⟩ := hp m
    refine ⟨z, ?_⟩
    funext i
    simp only [ψ, ψL, LinearMap.coe_comp, Function.comp_apply, hm, LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply, hc]
  let g : Set.range f → (Fin (finrank O F) → O ⧸ I) := fun n => ψ (p (Classical.choose n.2))
  have hg : Function.Surjective g := by
    intro t
    obtain ⟨z, hz⟩ := hsurj t
    refine ⟨⟨f z, z, rfl⟩, ?_⟩
    have hz' : f (Classical.choose (⟨z, rfl⟩ : ∃ y, f y = f z)) = f z := Classical.choose_spec (⟨z, rfl⟩ : ∃ y, f y = f z)
    simp only [g]
    rw [hψ _ _ (hf _ _ hz')]
    exact hz
  have h1 := Nat.card_le_card_of_surjective g hg
  have h2 : Nat.card (Set.range f) ≤ Nat.card N := Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  rw [Nat.card_fun, Nat.card_fin, e] at h1
  exact h1.trans h2

section Gen

variable {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL]
  [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL]
  (A : GRep G Qp LL O) (L : Lattice (O := O) A.ρ)

open GlobalTheory.CompanionTheory.GrowthOfInvariants in

theorem redT_mem {ϖ : O} {r : ℕ} (hW : (fun x => ϖ ^ r • x) '' (L.T : Set A.V) ∈ nhds (0 : A.V))
    (hI : StableSub L (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥L.T)) (c : ↥(latticeCocycles L)) :
    redT L _ c ∈ quotientCocycles L _ hI := by
  obtain ⟨⟨hcont, hcoc⟩, _⟩ := c.2
  refine ⟨?_, ?_⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro g0
    have hW' : (fun x => ϖ ^ r • x) '' (L.T : Set A.V) ∈ nhds ((c : _ → A.V) g0 + -(c : _ → A.V) g0) := by
      rw [add_neg_cancel]
      exact hW
    filter_upwards [(hcont.tendsto g0).add_const (-(c : _ → A.V) g0) hW'] with g hg
    obtain ⟨x, hx, hxe⟩ := hg
    refine (Submodule.Quotient.eq _).mpr ?_
    have : (evT L g c - evT L g0 c : ↥L.T) = ϖ ^ r • (⟨x, hx⟩ : ↥L.T) := by
      apply Subtype.ext
      simp only [Submodule.coe_sub, SetLike.val_smul]
      have hxe' : ϖ ^ r • x = (c : _ → A.V) g + -(c : _ → A.V) g0 := hxe
      rw [hxe', sub_eq_add_neg]
      rfl
    rw [this]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) Submodule.mem_top
  · intro g h
    show Submodule.Quotient.mk (evT L (g * h) c) = Submodule.Quotient.mk (evT L g c) + actQ L _ hI g (Submodule.Quotient.mk (evT L h c))
    rw [actQ, Submodule.mapQ_apply, ← Submodule.Quotient.mk_add]
    congr 1
    apply Subtype.ext
    exact hcoc g h

open GlobalTheory.CompanionTheory.GrowthOfInvariants in

theorem exists_div_class [IsDomain O] [IsFractionRing O LL] {a : O} (ha : a ≠ 0)
    (hI : StableSub L (Ideal.span {a} • ⊤ : Submodule O ↥L.T)) (c : ↥(latticeCocycles L))
    (hc : redT L (Ideal.span {a} • ⊤ : Submodule O ↥L.T) c ∈ BQ L _ hI) :
    ∃ w : LatticeCohomology L, (Submodule.Quotient.mk c : LatticeCohomology L) = a • w := by
  obtain ⟨t, ht⟩ := hc
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ t
  have hd : ∀ g, ∃ y : ↥L.T, a • y = evT L g c - (actT L g x - x) := by
    intro g
    have h1 := congrFun ht g
    simp only [LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.id_apply] at h1
    change actQ L _ hI g (Submodule.Quotient.mk x) - Submodule.Quotient.mk x = Submodule.Quotient.mk (evT L g c) at h1
    rw [actQ, Submodule.mapQ_apply, ← Submodule.Quotient.mk_sub, eq_comm, Submodule.Quotient.eq,
      Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at h1
    obtain ⟨y, _, hy⟩ := h1
    exact ⟨y, hy⟩
  choose y hy using hd
  obtain ⟨⟨hcont, hcoc⟩, _⟩ := c.2
  set α : LL := algebraMap O LL a with hαdef
  have hα : α ≠ 0 := fun h => ha ((IsFractionRing.injective O LL) (h.trans (map_zero _).symm))
  have hyV : ∀ g, a • ((y g : ↥L.T) : A.V) = (c : G → A.V) g - (A.ρ g (x : A.V) - (x : A.V)) := by
    intro g
    have := congrArg Subtype.val (hy g)
    exact this
  have hyL : ∀ g, α • ((y g : ↥L.T) : A.V) = (c : G → A.V) g - (A.ρ g (x : A.V) - (x : A.V)) := by
    intro g
    rw [hαdef, algebraMap_smul]
    exact hyV g
  let e : G → A.V := fun g => (y g : A.V)
  have he_form : e = fun g => α⁻¹ • ((c : G → A.V) g + (-1 : LL) • A.ρ g (x : A.V) + (x : A.V)) := by
    funext g
    have h2 : (c : G → A.V) g + (-1 : LL) • A.ρ g (x : A.V) + (x : A.V) = α • e g := by
      rw [hyL g, neg_one_smul]
      abel
    rw [h2, inv_smul_smul₀ hα]
  have he : e ∈ latticeCocycles L := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [he_form]
      exact ((hcont.add ((A.cont (x : A.V)).const_smul (-1 : LL))).add continuous_const).const_smul α⁻¹
    · intro g h
      apply smul_right_injective A.V hα
      simp only [smul_add, e, hyL, ← map_smul, hcoc, map_mul, Module.End.mul_apply, map_sub]
      abel
    · intro g _
      exact (y g).2
  refine ⟨Submodule.Quotient.mk ⟨e, he⟩, ?_⟩
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, Submodule.mem_comap]
  refine ⟨x, x.2, ?_⟩
  funext g
  change A.ρ g (x : A.V) - (x : A.V) = (c : G → A.V) g - a • e g
  rw [show a • e g = a • ((y g : ↥L.T) : A.V) from rfl, hyV g, sub_sub_cancel]

end Gen

theorem card_lower_bound : ∀ (D : D7) (l : ℕ) [Fact l.Prime] (K : FinExt l), TateFiniteness ((D.loc l).PD K) → FinZQ ((D.loc l).PD K) → ∀ (LL : Type) [Field LL] [Algebra ℚ_[l] LL] [TopologicalSpace LL] (O : Type) [CommRing O] [Algebra O LL], GoodO (Qp := ℚ_[l]) LL O → ∀ (A : GRep ↥(GK K) ℚ_[l] LL O) (LA : Lattice (O := O) A.ρ), ∀ ϖ : O, Irreducible ϖ → ∀ (r : ℕ) (hI : StableSub LA (Ideal.span {ϖ ^ r} • ⊤ : Submodule O ↥LA.T)), Nat.card (O ⧸ Ideal.span {ϖ}) ^ (r * finrank O (LatticeCohomology LA)) ≤ Nat.card (QuotientCohomology LA _ hI) := by
  intro D l _ K hfin hZ LL _ _ _ O _ _ hO A LA ϖ hϖ r hI
  obtain ⟨⟨hD, hV, hF⟩, -⟩ := id hO
  obtain ⟨-, hB, -⟩ := GlobalTheory.T.lattice_open_compact_nhds_basis D l K LL O hO A LA ϖ hϖ
  have hW : (fun x => ϖ ^ r • x) '' (LA.T : Set A.V) ∈ nhds (0 : A.V) := hB.mem_of_mem trivial
  have := hfin LL O hO A LA
  have := hZ LL O hO A LA ϖ hϖ r hI
  have : Finite (QuotientCohomology LA _ hI) := Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
  rw [pow_mul, ← GlobalTheory.CompanionTheory.GrowthOfInvariants.card_quot_pow ϖ hϖ.ne_zero r]
  refine card_pow_le (ϖ ^ r) (fun c : ↥(latticeCocycles LA) => (Submodule.Quotient.mk c : LatticeCohomology LA))
    (Submodule.Quotient.mk_surjective _)
    (fun c => (Submodule.Quotient.mk ⟨redT LA _ c, redT_mem A LA hW hI c⟩ : QuotientCohomology LA _ hI)) ?_
  intro x y h
  rw [← Submodule.Quotient.mk_sub]
  refine exists_div_class A LA (pow_ne_zero r hϖ.ne_zero) hI _ ?_
  rw [map_sub]
  have h' := (Submodule.Quotient.eq _).1 h
  exact h'

end PositivityTheory.LocalTateOrthogonality.Bk
end

-- bundled from Development.WeilBound.CoreStatements.EulerCharacteristicCounts.GcohCmp
section
open CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal ValuativeRel

namespace PositivityTheory.LocalTateOrthogonality.Gcoh

theorem gcRep : SgcRep := by
  intro G _ _ _ R _ M _ _ _ _ rho hrho
  letI : Module (ULift.{0} ℤ) M := Module.compHom M (ULift.ringEquiv : ULift.{0} ℤ ≃+* ℤ).toRingHom
  let σ : Representation (ULift.{0} ℤ) G M :=
    { toFun := fun g =>
        { toFun := rho g
          map_add' := map_add _
          map_smul' := fun c m => map_zsmul (rho g) c.down m }
      map_one' := LinearMap.ext fun m => by
        change rho 1 m = m
        rw [map_one]; rfl
      map_mul' := fun g h => LinearMap.ext fun m => by
        change rho (g * h) m = rho g (rho h m)
        rw [map_mul]; rfl }
  refine ⟨Rep.of σ, ⟨fun a => ?_⟩, AddEquiv.refl M, fun g m => rfl⟩
  have hc : Continuous fun g : G => rho g (a : M) :=
    hrho.comp (continuous_id.prodMk continuous_const)
  exact (isOpen_discrete {(a : M)}).preimage hc

attribute [local instance 2000] Rep.hV2

section

variable {k G : Type} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  (A : Rep.{0} k G) (e : M ≃+ A.V)

omit [IsTopologicalGroup G] in
theorem lc_of_cont {X : Type} [TopologicalSpace X] {f : X → M} (hf : Continuous f) :
    IsLocallyConstant fun s => e (f s) :=
  ((IsLocallyConstant.iff_continuous f).2 hf).comp e

omit [IsTopologicalGroup G] in
theorem cont_of_lc {X : Type} [TopologicalSpace X] {f : X → A.V} (hf : IsLocallyConstant f) :
    Continuous fun s => e.symm (f s) :=
  (hf.comp e.symm).continuous

end

theorem gcn : Sgcn := by
  intro G _ _ _ R _ M _ _ _ _ rho A _ e he n
  let φ : Zn rho n →+ ((Fin n → G) → A) :=
    AddMonoidHom.mk' (fun z s => e (z.1 s)) (fun z z' => funext fun s => map_add e _ _)
  have hφ : ∀ z s, φ z s = e (z.1 s) := fun _ _ => rfl
  obtain ⟨e', -⟩ := core_quot A ((Bn rho n).comap (Zn rho n).subtype) n φ
    (fun z => exists_coc A n _ (lc_of_cont A e z.2.1) (by
      have hz : dn rho n z.1 = 0 := z.2.2
      refine (d_comp rho A e he n z.1).trans ?_
      funext s
      rw [hz]
      exact map_zero e))
    (fun x => by
      refine ⟨⟨fun s => e.symm (cochainOf A (cocycleι A n x) s),
        cont_of_lc A e (isLocallyConstant_cochainOf _), ?_⟩, ?_⟩
      · have h := d_comp rho A e he n fun s => e.symm (cochainOf A (cocycleι A n x) s)
        simp only [AddEquiv.apply_symm_apply] at h
        rw [d_cocycleι] at h
        change dn rho n _ = 0
        funext s
        apply e.injective
        rw [← congrFun h s]
        exact (map_zero e).symm
      · funext s
        exact (e.apply_symm_apply _).symm)
    (fun z x hx => by
      cases n with
      | zero =>
        rw [pi_zero_eq_zero_iff, hx]
        change _ ↔ z.1 = 0
        constructor
        · intro h
          funext s
          exact e.map_eq_zero_iff.1 (congrFun h s)
        · intro h
          funext s
          rw [hφ, h]
          exact map_zero e
      | succ n =>
        rw [pi_succ_eq_zero_iff, hx]
        constructor
        · rintro ⟨w, hw, h⟩
          refine ⟨fun s => e.symm (w s), cont_of_lc A e hw, ?_⟩
          have h' := d_comp rho A e he n fun s => e.symm (w s)
          simp only [AddEquiv.apply_symm_apply] at h'
          funext s
          apply e.injective
          exact (congrFun h' s).symm.trans (congrFun h s)
        · rintro ⟨c, hc, h⟩
          refine ⟨fun s => e (c s), lc_of_cont A e hc, (d_comp rho A e he n c).trans ?_⟩
          funext s
          rw [h]
          rfl)
  exact ⟨e'⟩

theorem gc0 : Sgc0 := by
  intro G _ _ _ R _ M _ _ _ _ rho A _ e he
  let φ : H0 rho →+ ((Fin 0 → G) → A) :=
    AddMonoidHom.mk' (fun z _ => e z.1) (fun z z' => funext fun s => map_add e _ _)
  have hex : ∀ z, ∃ x : cocycles A 0, cochainOf A (cocycleι A 0 x) = φ z := fun z =>
    exists_coc A 0 _ (IsLocallyConstant.const _) (by
      refine (d_comp rho A e he 0 fun _ => z.1).trans ?_
      funext s
      rw [dn_zero, z.2 (s 0), sub_self]
      exact map_zero e)
  obtain ⟨f, hs, hf⟩ := core_hom A 0 φ hex (fun x => by
    refine ⟨⟨e.symm (cochainOf A (cocycleι A 0 x) default), fun g => ?_⟩, ?_⟩
    · have h := d_comp rho A e he 0 fun s => e.symm (cochainOf A (cocycleι A 0 x) s)
      simp only [AddEquiv.apply_symm_apply] at h
      rw [d_cocycleι] at h
      have h' := congrFun h (fun _ => g)
      rw [dn_zero] at h'
      exact sub_eq_zero.1 (e.map_eq_zero_iff.1 h'.symm)
    · funext s
      rw [Subsingleton.elim s default]
      exact (e.apply_symm_apply _).symm)
  refine ⟨AddEquiv.ofBijective f ⟨?_, hs⟩, fun m x h => hf m x (funext h)⟩
  rw [injective_iff_map_eq_zero]
  intro z hz
  obtain ⟨x, hx⟩ := hex z
  rw [hf z x hx, pi_zero_eq_zero_iff, hx] at hz
  exact Subtype.ext (e.map_eq_zero_iff.1 (congrFun hz default))

theorem gc1 : Sgc1 := by
  intro G _ _ _ R _ M _ _ _ _ rho A _ e he
  let φ : Z1 rho →+ ((Fin 1 → G) → A) :=
    AddMonoidHom.mk' (fun z s => e (z.1 (s 0))) (fun z z' => funext fun s => map_add e _ _)
  have hex : ∀ z, ∃ x : cocycles A 1, cochainOf A (cocycleι A 1 x) = φ z := fun z =>
    exists_coc A 1 _ (lc_of_cont A e (z.2.1.comp (continuous_apply 0))) (by
      refine (d_comp rho A e he 1 fun s => z.1 (s 0)).trans ?_
      funext s
      rw [dn_one, z.2.2 (s 0) (s 1)]
      rw [show ∀ a b : M, b - (a + b) + a = 0 from fun a b => by abel]
      exact map_zero e)
  have hv : ∀ s : Fin 1 → G, s = fun _ => s 0 := fun s => funext fun i => by
    rw [Subsingleton.elim i 0]
  obtain ⟨e', he'⟩ := core_quot A ((B1 rho).comap (Z1 rho).subtype) 1 φ hex
    (fun x => by
      have hx : cochainOf A (cocycleι A 1 x) =
          fun s => e (e.symm (cochainOf A (cocycleι A 1 x) fun _ => s 0)) := by
        funext s
        rw [e.apply_symm_apply, ← hv]
      refine ⟨⟨fun g => e.symm (cochainOf A (cocycleι A 1 x) fun _ => g),
        (cont_of_lc A e (isLocallyConstant_cochainOf _)).comp
          (continuous_pi fun _ => continuous_id), fun g g' => ?_⟩, hx⟩
      have h := d_comp rho A e he 1 fun s => e.symm (cochainOf A (cocycleι A 1 x) fun _ => s 0)
      rw [← hx, d_cocycleι] at h
      have h' := congrFun h ![g, g']
      rw [dn_one rho (fun g => e.symm (cochainOf A (cocycleι A 1 x) fun _ => g))] at h'
      have h2 := e.map_eq_zero_iff.1 h'.symm
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h2
      rw [← sub_eq_zero, ← neg_eq_zero, ← h2]
      abel)
    (fun z x hx => by
      rw [pi_succ_eq_zero_iff, hx]
      constructor
      · rintro ⟨w, hw, h⟩
        refine ⟨e.symm (w default), ?_⟩
        have h' := d_comp rho A e he 0 fun s => e.symm (w s)
        simp only [AddEquiv.apply_symm_apply] at h'
        funext g
        apply e.injective
        have h2 := (congrFun h' fun _ => g).symm.trans (congrFun h fun _ => g)
        rw [dn_zero] at h2
        exact h2
      · rintro ⟨m, h⟩
        refine ⟨fun _ => e m, IsLocallyConstant.const _, (d_comp rho A e he 0 fun _ => m).trans ?_⟩
        funext s
        rw [dn_zero]
        exact congrArg e (congrFun h (s 0)))
  refine ⟨e', fun z => ?_, fun z x h => he' z x (funext h)⟩
  obtain ⟨x, hx⟩ := hex z
  exact ⟨x, congrFun hx⟩

theorem gc2 : Sgc2 := by
  intro G _ _ _ R _ M _ _ _ _ rho A _ e he
  let φ : Z2 rho →+ ((Fin 2 → G) → A) :=
    AddMonoidHom.mk' (fun z s => e (z.1 (s 0, s 1))) (fun z z' => funext fun s => map_add e _ _)
  have hex : ∀ z, ∃ x : cocycles A 2, cochainOf A (cocycleι A 2 x) = φ z := fun z =>
    exists_coc A 2 _
      (lc_of_cont A e (z.2.1.comp ((continuous_apply 0).prodMk (continuous_apply 1)))) (by
      refine (d_comp rho A e he 2 fun s => z.1 (s 0, s 1)).trans ?_
      funext s
      rw [dn_two, z.2.2 (s 0) (s 1) (s 2)]
      exact map_zero e)
  have hv : ∀ s : Fin 1 → G, s = fun _ => s 0 := fun s => funext fun i => by
    rw [Subsingleton.elim i 0]
  have hv2 : ∀ s : Fin 2 → G, s = ![s 0, s 1] := fun s => funext fun i => by
    fin_cases i <;> rfl
  obtain ⟨e', he'⟩ := core_quot A ((B2 rho).comap (Z2 rho).subtype) 2 φ hex
    (fun x => by
      have hx : cochainOf A (cocycleι A 2 x) =
          fun s => e (e.symm (cochainOf A (cocycleι A 2 x) ![s 0, s 1])) := by
        funext s
        rw [e.apply_symm_apply, ← hv2]
      refine ⟨⟨fun p => e.symm (cochainOf A (cocycleι A 2 x) ![p.1, p.2]),
        (cont_of_lc A e (isLocallyConstant_cochainOf _)).comp
          (continuous_pi fun i => by
            fin_cases i
            · exact continuous_fst
            · exact continuous_snd), fun g g' g'' => ?_⟩, hx⟩
      have h := d_comp rho A e he 2 fun s => e.symm (cochainOf A (cocycleι A 2 x) ![s 0, s 1])
      rw [← hx, d_cocycleι] at h
      have h' := congrFun h ![g, g', g'']
      rw [dn_two rho (fun p => e.symm (cochainOf A (cocycleι A 2 x) ![p.1, p.2]))] at h'
      exact e.map_eq_zero_iff.1 h'.symm)
    (fun z x hx => by
      rw [pi_succ_eq_zero_iff, hx]
      constructor
      · rintro ⟨w, hw, h⟩
        refine ⟨fun g => e.symm (w fun _ => g),
          (cont_of_lc A e hw).comp (continuous_pi fun _ => continuous_id), ?_⟩
        have hw' : w = fun s => e (e.symm (w fun _ => s 0)) := by
          funext s
          rw [e.apply_symm_apply, ← hv]
        have h' := d_comp rho A e he 1 fun s => e.symm (w fun _ => s 0)
        rw [← hw'] at h'
        funext p
        apply e.injective
        have h2 := (congrFun h' ![p.1, p.2]).symm.trans (congrFun h ![p.1, p.2])
        rw [dn_one rho (fun g => e.symm (w fun _ => g))] at h2
        exact h2
      · rintro ⟨c, hc, h⟩
        refine ⟨fun s => e (c (s 0)), lc_of_cont A e (Continuous.comp hc (continuous_apply 0)),
          (d_comp rho A e he 1 fun s => c (s 0)).trans ?_⟩
        funext s
        rw [dn_one]
        exact congrArg e (congrFun h (s 0, s 1)))
  refine ⟨e', fun z => ?_, fun z x h => he' z x (funext h)⟩
  obtain ⟨x, hx⟩ := hex z
  exact ⟨x, congrFun hx⟩

end PositivityTheory.LocalTateOrthogonality.Gcoh
end

