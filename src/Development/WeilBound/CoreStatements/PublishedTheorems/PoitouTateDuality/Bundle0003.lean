import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsDefs
import GroundTheory.ProfiniteCohomology.PoitouTate.PoitouTateNineTermGs
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0410
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0045

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.CupCompareDegreeOneOne
section
noncomputable section

open CategoryTheory MonoidalCategory TensorProduct GroundTheory.ProfCoh ReciprocityTheory.Gal

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2

theorem cup_compare_degree_one_one {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {R : Type}
    [CommRing R] {M M' P : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [AddCommGroup M'] [Module R M']
    [TopologicalSpace M'] [IsTopologicalAddGroup M'] [ContinuousConstSMul R M'] [AddCommGroup P]
    [Module R P] [TopologicalSpace P] [IsTopologicalAddGroup P] [ContinuousConstSMul R P]
    (rho : Representation R G M) (rho' : Representation R G M') (rhoP : Representation R G P)
    (b : M →ₗ[R] M' →ₗ[R] P) (hb : Continuous fun p : M × M' => b p.1 p.2)
    (hbe : ∀ g x y, b (rho g x) (rho' g y) = rhoP g (b x y)) (hc : ContAction rho')
    (A B C : Rep.{0} (ULift.{0} ℤ) G) [IsDiscreteRep A] [IsDiscreteRep B] [IsDiscreteRep C]
    (eA : M ≃+ A.V) (eB : M' ≃+ B.V) (eC : P ≃+ C.V)
    (heB : ∀ g m, eB (rho' g m) = B.ρ g (eB m))
    (μ : A ⊗ B ⟶ C) (hbμ : ∀ x y, eC (b x y) = μ.hom (eA x ⊗ₜ[ULift.{0} ℤ] eB y))
    (z : Z1 rho) (z' : Z1 rho') (x : cocycles A 1) (x' : cocycles B 1)
    (hx : ∀ s, cochainOf A (cocycleι A 1 x) s = eA (z.1 (s 0)))
    (hx' : ∀ s, cochainOf B (cocycleι B 1 x') s = eB (z'.1 (s 0))) :
    ∃ y : cocycles C 2,
      (∀ s, cochainOf C (cocycleι C 2 y) s = eC ((cupCocycleZ1Z1 rho rho' rhoP b hb hbe hc z z').1 (s 0, s 1))) ∧
      cohomologyπ C 2 y = cupPairing μ (rfl : 1 + 1 = 2)
        (cohomologyπ A 1 x) (cohomologyπ B 1 x') := by
  refine ⟨HomologicalComplex.cyclesMap (cochainsMap μ) 2 (cupCocycles (rfl : 1 + 1 = 2) x x'),
    fun s => ?_, (cupPairing_cohomologyπ μ rfl x x').symm⟩
  rw [cochainOf_cocycleι_cyclesMap_cupCocycles, hx, hx', cupCocycleZ1Z1_apply, hbμ, heB]
  have h1 : Fin.partialProd s ⟨1, by omega⟩ = s 0 := by
    show Fin.partialProd s (Fin.succ 0) = s 0
    rw [Fin.partialProd_succ]
    show Fin.partialProd s 0 * s 0 = s 0
    rw [Fin.partialProd_zero, one_mul]
  rw [h1]
  rfl

end PositivityTheory.Lit1.PTN
end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.FinalGenDefs
section
noncomputable section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh GroundTheory.Global GroundTheory.LocalField
  ReciprocityTheory.Gal Formalism.ConjugateSelfDual GlobalTheory.Published GlobalTheory.Published.PoitouTate PositivityTheory.PoitouTateConclusion

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2

def urChar (K Ω : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field Ω] [Algebra K Ω] [HasUnramifiedRoots K Ω] (N : ℕ+) (σ : Gal(Ω/K)) : ZMod (N : ℕ) :=
  GroundTheory.LocalField.Abstract.ProfiniteInteger.proj N (Multiplicative.toAdd (unramifiedDegree K Ω σ))

theorem zmodToQZ_eq_nsmul {n : ℕ} [NeZero n] (c : ZMod n) :
    zmodToQZ n c = c.val • zmodToQZ n 1 := by
  conv_lhs => rw [← ZMod.natCast_zmod_val c]
  rw [← nsmul_one, map_nsmul]

end PositivityTheory.Lit1.PTN
end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.LocalCmp2
section
noncomputable section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
  PositivityTheory.PoitouTateConclusion

namespace PositivityTheory.Lit1.PTN

theorem localCmp2' (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField K]
    [IsAlgClosure K (AlgebraicClosure ℚ)] (S : Finset (HeightOneSpectrum (𝓞 K)))
    (Av : S → ValuationSubring (AlgebraicClosure ℚ)) (hAv : ∀ v, IsPlaceOver (Av v) v.1)
    (e : GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 K))) ≃ₜ*
        GroundTheory.ProfCoh.galUnramifiedOutside K (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 K))))
    (he : ∀ (σ : G K (AlgebraicClosure ℚ))
        (y : GroundTheory.ProfCoh.maxUnramifiedOutside K (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 K)))),
        ((e (toGS (AlgebraicClosure ℚ) _ σ) y :
          GroundTheory.ProfCoh.maxUnramifiedOutside K (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 K)))) :
            AlgebraicClosure ℚ) = σ (y : AlgebraicClosure ℚ)) :
    ∃ (ιs : ∀ v : (S : Set (HeightOneSpectrum (𝓞 K))), AlgebraicClosure ℚ →ₐ[K]
        AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K))
      (ev : ∀ v : S, (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K) ≃ₐ[
          (v : HeightOneSpectrum (𝓞 K)).adicCompletion K]
          AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K)) ≃* Dec (F := K) (Av v)),
      (∀ v, Continuous (ev v) ∧ Continuous (ev v).symm) ∧
      (∀ (v : S) σ x, ιs ⟨v.1, Finset.mem_coe.2 v.2⟩
        (((ev v σ : Dec (F := K) (Av v)) : G K (AlgebraicClosure ℚ)) x) =
          σ (ιs ⟨v.1, Finset.mem_coe.2 v.2⟩ x)) ∧
      ∀ (v : S) σ, e (locFam S Av v (ev v σ)) =
        GroundTheory.ProfCoh.gsFinFamily (S : Set (HeightOneSpectrum (𝓞 K))) ιs ⟨v.1, Finset.mem_coe.2 v.2⟩ σ := by
  classical
  have key : ∀ v : S, ∃ (ι : AlgebraicClosure ℚ →ₐ[K]
        AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K))
      (ev : (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K) ≃ₐ[
          (v : HeightOneSpectrum (𝓞 K)).adicCompletion K]
          AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K)) ≃* Dec (F := K) (Av v)),
      Continuous ev ∧ Continuous ev.symm ∧
        ∀ σ x, ι (((ev σ : Dec (F := K) (Av v)) : G K (AlgebraicClosure ℚ)) x) = σ (ι x) :=
    fun v => GlobalTheory.CompanionTheory.DecGal.exists_algHom_mulEquiv_dec K (AlgebraicClosure ℚ) (Av v) v.1 (hAv v)
  choose ι ev hc hc' hι using key
  refine ⟨fun w => ι ⟨w.1, Finset.mem_coe.1 w.2⟩, ev, fun v => ⟨hc v, hc' v⟩, fun v σ x => hι v σ x, fun v σ => ?_⟩
  apply AlgEquiv.ext
  intro y
  apply Subtype.ext
  apply (ι v).injective
  have h1 := GroundTheory.ProfCoh.gsFinFamily_apply (S : Set (HeightOneSpectrum (𝓞 K)))
    (fun w => ι ⟨w.1, Finset.mem_coe.1 w.2⟩) ⟨v.1, Finset.mem_coe.2 v.2⟩ σ y
  have h2 := he ((ev v σ : Dec (F := K) (Av v)) : G K (AlgebraicClosure ℚ)) y
  refine Eq.trans ?_ h1.symm
  change ι v ((e (toGS (AlgebraicClosure ℚ) _
    ((ev v σ : Dec (F := K) (Av v)) : G K (AlgebraicClosure ℚ))) y :
      GroundTheory.ProfCoh.maxUnramifiedOutside K (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 K)))) :
        AlgebraicClosure ℚ) = _
  rw [h2, hι]

end PositivityTheory.Lit1.PTN
end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PfNineAddFSCReindex
section
noncomputable section

open CategoryTheory GroundTheory.ProfCoh

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2

def reindexAdd {α β : Type} (P : β → Type) [∀ b, AddCommGroup (P b)] (e : α ≃ β) :
    (∀ a, P (e a)) ≃+ (∀ b, P b) :=
  { Equiv.piCongrLeft P e with
    map_add' := fun f g => by
      funext b
      obtain ⟨a, rfl⟩ := e.surjective b
      simp only [Equiv.toFun_as_coe, Pi.add_apply, Equiv.piCongrLeft_apply_apply] }

theorem reindexAdd_apply {α β : Type} (P : β → Type) [∀ b, AddCommGroup (P b)] (e : α ≃ β)
    (f : ∀ a, P (e a)) (a : α) : reindexAdd P e f (e a) = f a :=
  Equiv.piCongrLeft_apply_apply P e f a

theorem reindexAdd_symm_apply {α β : Type} (P : β → Type) [∀ b, AddCommGroup (P b)] (e : α ≃ β)
    (g : ∀ b, P b) (a : α) : (reindexAdd P e).symm g a = g (e a) := by
  have h := reindexAdd_apply P e ((reindexAdd P e).symm g) a
  rw [AddEquiv.apply_symm_apply] at h
  exact h.symm

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ι : Type} {Hv : ι → Type} [∀ v, Group (Hv v)] [∀ v, TopologicalSpace (Hv v)]
  [∀ v, IsTopologicalGroup (Hv v)] (φ : ∀ v, Hv v →ₜ* G)

theorem ptLocalDualMap_reindex [Fintype ι] {κ : Type} [Fintype κ] (e : κ ≃ ι)
    (D : Rep.{0} (ULift.{0} ℤ) G) [IsDiscreteRep D] (M : Rep.{0} (ULift.{0} ℤ) G) [IsDiscreteRep M]
    [Finite M] (inv : ∀ v, cohomology (Rep.res (φ v).toMonoidHom D) 2 →+ QZ) {r s : ℕ}
    (h : r + s = 2) (ξ : ∀ k, cohomology (Rep.res (φ (e k)).toMonoidHom M) r)
    (y : cohomology (dualRep D M) s) :
    ptLocalDualMap φ D M inv h
        (reindexAdd (fun v => cohomology (Rep.res (φ v).toMonoidHom M) r) e ξ) y =
      ∑ k, ptLocalPairing φ D M inv (e k) h (ξ k) (ptRes φ (dualRep D M) (e k) s y) := by
  rw [ptLocalDualMap_apply]
  refine (Fintype.sum_equiv e _ _ (fun k => ?_)).symm
  rw [reindexAdd_apply]

theorem ptGlobalToLocal_reindex {κ : Type} (e : κ ≃ ι) (M : Rep.{0} (ULift.{0} ℤ) G) [IsDiscreteRep M]
    (r : ℕ) (x : cohomology M r) (k : κ) :
    (reindexAdd (fun v => cohomology (Rep.res (φ v).toMonoidHom M) r) e).symm
      ((ptGlobalToLocal φ M r).hom x) k = ptRes φ M (e k) r x := by
  rw [reindexAdd_symm_apply, ptGlobalToLocal_apply]

theorem locSq_reindex {κ : Type} (e : κ ≃ ι) (M : Rep.{0} (ULift.{0} ℤ) G) [IsDiscreteRep M] (r : ℕ)
    {X : Type} [AddCommGroup X] {Xk : κ → Type} [∀ k, AddCommGroup (Xk k)]
    (res : ∀ k, X →+ Xk k) (E : X ≃+ cohomology M r)
    (Ev : ∀ k, Xk k ≃+ cohomology (Rep.res (φ (e k)).toMonoidHom M) r)
    (sq : ∀ k x, Ev k (res k x) = ptRes φ M (e k) r (E x)) (x : X) :
    (ptGlobalToLocal φ M r).hom (E x) =
      reindexAdd (fun v => cohomology (Rep.res (φ v).toMonoidHom M) r) e (fun k => Ev k (res k x)) := by
  apply (reindexAdd (fun v => cohomology (Rep.res (φ v).toMonoidHom M) r) e).symm.injective
  rw [AddEquiv.symm_apply_apply]
  funext k
  rw [ptGlobalToLocal_reindex, sq]

theorem trSq_reindex [Fintype ι] {κ : Type} [Fintype κ] (e : κ ≃ ι)
    (D : Rep.{0} (ULift.{0} ℤ) G) [IsDiscreteRep D] (M : Rep.{0} (ULift.{0} ℤ) G) [IsDiscreteRep M]
    [Finite M] (inv : ∀ v, cohomology (Rep.res (φ v).toMonoidHom D) 2 →+ QZ) {r s : ℕ}
    (h : r + s = 2) {N : ℕ} [NeZero N] {Xk : κ → Type} [∀ k, AddCommGroup (Xk k)]
    [∀ k, Module (ZMod N) (Xk k)] {Y : Type} [AddCommGroup Y] [Module (ZMod N) Y]
    {Yk : κ → Type} [∀ k, AddCommGroup (Yk k)] [∀ k, Module (ZMod N) (Yk k)]
    (resY : ∀ k, Y →ₗ[ZMod N] Yk k) (P : ∀ k, Xk k →ₗ[ZMod N] Yk k →ₗ[ZMod N] ZMod N)
    (Ex : ∀ k, Xk k ≃+ cohomology (Rep.res (φ (e k)).toMonoidHom M) r)
    (Ey : Y ≃+ cohomology (dualRep D M) s)
    (Eyk : ∀ k, Yk k ≃+ cohomology (Rep.res (φ (e k)).toMonoidHom (dualRep D M)) s)
    (hres : ∀ k y, Eyk k (resY k y) = ptRes φ (dualRep D M) (e k) s (Ey y)) (ε : ℤ)
    (hQ : ∀ k a b, ptLocalPairing φ D M inv (e k) h (Ex k a) (Eyk k b) = ε • zmodToQZ N (P k a b))
    (x : ∀ k, Xk k) (y : cohomology (dualRep D M) s) :
    ptLocalDualMap φ D M inv h
        (reindexAdd (fun v => cohomology (Rep.res (φ v).toMonoidHom M) r) e (fun k => Ex k (x k))) y =
      ε • zmodToQZ N (∑ k, P k (x k) (resY k (Ey.symm y))) := by
  rw [ptLocalDualMap_reindex, map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← hQ, hres, AddEquiv.apply_symm_apply]

def finsetCoeEquiv {α : Type} (S : Finset α) : S ≃ (S : Set α) where
  toFun v := ⟨v.1, Finset.mem_coe.2 v.2⟩
  invFun w := ⟨w.1, Finset.mem_coe.1 w.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem ptRes_comp_reindex {κ : Type} (e : κ ≃ ι) (M : Rep.{0} (ULift.{0} ℤ) G) [IsDiscreteRep M]
    (k : κ) (r : ℕ) (x : cohomology M r) :
    ptRes (fun k => φ (e k)) M k r x = ptRes φ M (e k) r x := rfl

end PositivityTheory.Lit1.PTN
end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsBidual
section
noncomputable section

open CategoryTheory GroundTheory.ProfCoh

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2

theorem bidualCmp {G : Type} [Group G] (D A : Rep.{0} (ULift.{0} ℤ) G) (N : ℕ) [NeZero N]
    (hD : Nonempty (D ≃+ ZMod N)) [Finite A] (hA : ∀ m : A, N • m = 0) :
    ∃ eB : A.V ≃+ (dualRep D (dualRep D A)).V,
      ∀ g a, eB (A.ρ g a) = (dualRep D (dualRep D A)).ρ g (eB a) := by
  have hb := bijective_toDualDual (D := D) (M := A) hD hA
  let f : A.V →+ (dualRep D (dualRep D A)).V :=
    { toFun := (toDualDual D A).hom, map_zero' := map_zero _, map_add' := map_add _ }
  refine ⟨AddEquiv.ofBijective f hb, fun g a => ?_⟩
  exact Rep.hom_comm_apply (toDualDual D A) g a

end PositivityTheory.Lit1.PTN
end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsCup
section
noncomputable section

open CategoryTheory MonoidalCategory TensorProduct GroundTheory.ProfCoh ReciprocityTheory.Gal

namespace PositivityTheory.Lit1.PTN

attribute [local instance 2000] Rep.hV2

theorem cup_compare_degree_zero_two {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {R : Type}
    [CommRing R] {M M' P : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [AddCommGroup M'] [Module R M']
    [TopologicalSpace M'] [IsTopologicalAddGroup M'] [ContinuousConstSMul R M'] [AddCommGroup P]
    [Module R P] [TopologicalSpace P] [IsTopologicalAddGroup P] [ContinuousConstSMul R P]
    (rho : Representation R G M) (rho' : Representation R G M') (rhoP : Representation R G P)
    (b : M →ₗ[R] M' →ₗ[R] P) (hb : Continuous fun p : M × M' => b p.1 p.2)
    (hbe : ∀ g x y, b (rho g x) (rho' g y) = rhoP g (b x y))
    (A B C : Rep.{0} (ULift.{0} ℤ) G) [IsDiscreteRep A] [IsDiscreteRep B] [IsDiscreteRep C]
    (eA : M ≃+ A.V) (eB : M' ≃+ B.V) (eC : P ≃+ C.V)
    (heB : ∀ g m, eB (rho' g m) = B.ρ g (eB m))
    (μ : A ⊗ B ⟶ C) (hbμ : ∀ x y, eC (b x y) = μ.hom (eA x ⊗ₜ[ULift.{0} ℤ] eB y))
    (m : H0 rho) (z' : Z2 rho') (x : cocycles A 0) (x' : cocycles B 2)
    (hx : ∀ s, cochainOf A (cocycleι A 0 x) s = eA m.1)
    (hx' : ∀ s, cochainOf B (cocycleι B 2 x') s = eB (z'.1 (s 0, s 1))) :
    ∃ y : cocycles C 2,
      (∀ s, cochainOf C (cocycleι C 2 y) s = eC ((cupCocycleH0Z2 rho rho' rhoP b hb hbe m z').1 (s 0, s 1))) ∧
      cohomologyπ C 2 y = cupPairing μ (rfl : 0 + 2 = 2)
        (cohomologyπ A 0 x) (cohomologyπ B 2 x') := by
  refine ⟨HomologicalComplex.cyclesMap (cochainsMap μ) 2 (cupCocycles (rfl : 0 + 2 = 2) x x'),
    fun s => ?_, (cupPairing_cohomologyπ μ rfl x x').symm⟩
  rw [cochainOf_cocycleι_cyclesMap_cupCocycles, hx, hx', cupCocycleH0Z2_apply, hbμ]
  have h0 : Fin.partialProd s ⟨0, by omega⟩ = 1 := Fin.partialProd_zero s
  rw [h0, map_one]
  rfl

theorem cup_compare_degree_two_zero {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {R : Type}
    [CommRing R] {M M' P : Type} [AddCommGroup M] [Module R M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [ContinuousConstSMul R M] [AddCommGroup M'] [Module R M']
    [TopologicalSpace M'] [IsTopologicalAddGroup M'] [ContinuousConstSMul R M'] [AddCommGroup P]
    [Module R P] [TopologicalSpace P] [IsTopologicalAddGroup P] [ContinuousConstSMul R P]
    (rho : Representation R G M) (rho' : Representation R G M') (rhoP : Representation R G P)
    (b : M →ₗ[R] M' →ₗ[R] P) (hb : Continuous fun p : M × M' => b p.1 p.2)
    (hbe : ∀ g x y, b (rho g x) (rho' g y) = rhoP g (b x y))
    (A B C : Rep.{0} (ULift.{0} ℤ) G) [IsDiscreteRep A] [IsDiscreteRep B] [IsDiscreteRep C]
    (eA : M ≃+ A.V) (eB : M' ≃+ B.V) (eC : P ≃+ C.V)
    (heB : ∀ g m, eB (rho' g m) = B.ρ g (eB m))
    (μ : A ⊗ B ⟶ C) (hbμ : ∀ x y, eC (b x y) = μ.hom (eA x ⊗ₜ[ULift.{0} ℤ] eB y))
    (z : Z2 rho) (m : H0 rho') (x : cocycles A 2) (x' : cocycles B 0)
    (hx : ∀ s, cochainOf A (cocycleι A 2 x) s = eA (z.1 (s 0, s 1)))
    (hx' : ∀ s, cochainOf B (cocycleι B 0 x') s = eB m.1) :
    ∃ y : cocycles C 2,
      (∀ s, cochainOf C (cocycleι C 2 y) s = eC ((cupCocycleZ2H0 rho rho' rhoP b hb hbe z m).1 (s 0, s 1))) ∧
      cohomologyπ C 2 y = cupPairing μ (rfl : 2 + 0 = 2)
        (cohomologyπ A 2 x) (cohomologyπ B 0 x') := by
  refine ⟨HomologicalComplex.cyclesMap (cochainsMap μ) 2 (cupCocycles (rfl : 2 + 0 = 2) x x'),
    fun s => ?_, (cupPairing_cohomologyπ μ rfl x x').symm⟩
  rw [cochainOf_cocycleι_cyclesMap_cupCocycles, hx, hx', cupCocycleZ2H0_apply, hbμ, ← heB,
    (mem_riemannRochSpace_iff_regularAt_everywhere rho' m.1).1 m.2]

end PositivityTheory.Lit1.PTN
end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsDualQZ
section
noncomputable section

open GroundTheory.ProfCoh

namespace PositivityTheory.Lit1.PTN

theorem nsmul_eq_zero_of_zmod {N : ℕ} {X : Type} [AddCommGroup X] [Module (ZMod N) X] (a : X) :
    N • a = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (ZMod N), ZMod.natCast_self, zero_smul]

def dualQZ {N : ℕ} [NeZero N] {X Y : Type} [AddCommGroup X] [Module (ZMod N) X] [AddCommGroup Y]
    (E : X ≃+ Y) : Module.Dual (ZMod N) X ≃+ (Y →+ QZ) where
  toFun φ := (zmodToQZ N).comp (φ.toAddMonoidHom.comp E.symm.toAddMonoidHom)
  invFun ψ := (zmodOfQZ (ψ.comp E.toAddMonoidHom) (fun a => by
      rw [← map_nsmul, nsmul_eq_zero_of_zmod, map_zero])).toZModLinearMap N
  left_inv φ := LinearMap.ext fun a => zmodToQZ_injective (by
    simp [zmodToQZ_zmodOfQZ])
  right_inv ψ := AddMonoidHom.ext fun y => by
    simp [zmodToQZ_zmodOfQZ]
  map_add' φ φ' := AddMonoidHom.ext fun y => by simp

theorem dualQZ_apply {N : ℕ} [NeZero N] {X Y : Type} [AddCommGroup X] [Module (ZMod N) X]
    [AddCommGroup Y] (E : X ≃+ Y) (φ : Module.Dual (ZMod N) X) (y : Y) :
    dualQZ E φ y = zmodToQZ N (φ (E.symm y)) := rfl

end PositivityTheory.Lit1.PTN
end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsGsEquiv
section
noncomputable section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal Formalism.ConjugateSelfDual

namespace PositivityTheory.Lit1.PTN

theorem gsEquiv_toGS' (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField K]
    [IsAlgClosure K (AlgebraicClosure ℚ)] (S : Set (HeightOneSpectrum (𝓞 K))) :
    ∃ e : GS (AlgebraicClosure ℚ) S ≃ₜ*
        GroundTheory.ProfCoh.galUnramifiedOutside K (AlgebraicClosure ℚ) S,
      ∀ (σ : G K (AlgebraicClosure ℚ))
        (y : GroundTheory.ProfCoh.maxUnramifiedOutside K (AlgebraicClosure ℚ) S),
        ((e (toGS (AlgebraicClosure ℚ) S σ) y :
          GroundTheory.ProfCoh.maxUnramifiedOutside K (AlgebraicClosure ℚ) S) : AlgebraicClosure ℚ) =
          σ (y : AlgebraicClosure ℚ) := by
  have : IsGalois K (AlgebraicClosure ℚ) := IsAlgClosure.isGalois K (AlgebraicClosure ℚ)
  let E := maxUnramifiedOutside K (AlgebraicClosure ℚ) S
  let φ : G K (AlgebraicClosure ℚ) →* Gal(E/K) := AlgEquiv.restrictNormalHom E
  have hφs : Function.Surjective φ := AlgEquiv.restrictNormalHom_surjective (AlgebraicClosure ℚ)
  have hker : φ.ker = NS (AlgebraicClosure ℚ) S := by
    rw [GlobalTheory.CompanionTheory.Hypotheses₂.NS_eq_fixingSubgroup K (AlgebraicClosure ℚ) S]
    ext σ
    rw [MonoidHom.mem_ker, IntermediateField.mem_fixingSubgroup_iff]
    constructor
    · intro h x hx
      have h1 := AlgEquiv.restrictNormal_commutes σ E (⟨x, hx⟩ : E)
      have h2 : σ.restrictNormal E = 1 := h
      rw [h2] at h1
      exact h1.symm
    · intro h
      apply AlgEquiv.ext
      intro x
      apply Subtype.ext
      exact (AlgEquiv.restrictNormal_commutes σ E x).trans (h x.1 x.2)
  have hφc : Continuous φ := InfiniteGalois.restrictNormalHom_continuous E
  let q : GS (AlgebraicClosure ℚ) S ≃* Gal(E/K) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφs)
  have hq : Continuous q := continuous_coinduced_dom.2 hφc
  have : CompactSpace (G K (AlgebraicClosure ℚ)) := inferInstance
  have : CompactSpace (GS (AlgebraicClosure ℚ) S) := Quotient.compactSpace
  refine ⟨{ q with
    continuous_toFun := hq
    continuous_invFun := Continuous.continuous_symm_of_equiv_compact_to_t2 (f := q.toEquiv) hq },
    fun σ y => ?_⟩
  exact AlgEquiv.restrictNormal_commutes σ E y

end PositivityTheory.Lit1.PTN
end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsLocal
section
noncomputable section

open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate
  PositivityTheory.PoitouTateConclusion

namespace PositivityTheory.Lit1.PTN

theorem localCmp' (K : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField K]
    [IsAlgClosure K (AlgebraicClosure ℚ)] (S : Finset (HeightOneSpectrum (𝓞 K)))
    (Av : S → ValuationSubring (AlgebraicClosure ℚ)) (hAv : ∀ v, IsPlaceOver (Av v) v.1)
    (e : GS (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 K))) ≃ₜ*
        GroundTheory.ProfCoh.galUnramifiedOutside K (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 K))))
    (he : ∀ (σ : G K (AlgebraicClosure ℚ))
        (y : GroundTheory.ProfCoh.maxUnramifiedOutside K (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 K)))),
        ((e (toGS (AlgebraicClosure ℚ) _ σ) y :
          GroundTheory.ProfCoh.maxUnramifiedOutside K (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 K)))) :
            AlgebraicClosure ℚ) = σ (y : AlgebraicClosure ℚ)) :
    ∃ (ιs : ∀ v : (S : Set (HeightOneSpectrum (𝓞 K))), AlgebraicClosure ℚ →ₐ[K]
        AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K))
      (ev : ∀ v : S, (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K) ≃ₐ[
          (v : HeightOneSpectrum (𝓞 K)).adicCompletion K]
          AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K)) ≃* Dec (F := K) (Av v)),
      (∀ v, Continuous (ev v) ∧ Continuous (ev v).symm) ∧
      ∀ (v : S) σ, e (locFam S Av v (ev v σ)) =
        GroundTheory.ProfCoh.gsFinFamily (S : Set (HeightOneSpectrum (𝓞 K))) ιs ⟨v.1, Finset.mem_coe.2 v.2⟩ σ := by
  classical
  have key : ∀ v : S, ∃ (ι : AlgebraicClosure ℚ →ₐ[K]
        AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K))
      (ev : (AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K) ≃ₐ[
          (v : HeightOneSpectrum (𝓞 K)).adicCompletion K]
          AlgebraicClosure ((v : HeightOneSpectrum (𝓞 K)).adicCompletion K)) ≃* Dec (F := K) (Av v)),
      Continuous ev ∧ Continuous ev.symm ∧
        ∀ σ x, ι (((ev σ : Dec (F := K) (Av v)) : G K (AlgebraicClosure ℚ)) x) = σ (ι x) :=
    fun v => GlobalTheory.CompanionTheory.DecGal.exists_algHom_mulEquiv_dec K (AlgebraicClosure ℚ) (Av v) v.1 (hAv v)
  choose ι ev hc hc' hι using key
  refine ⟨fun w => ι ⟨w.1, Finset.mem_coe.1 w.2⟩, ev, fun v => ⟨hc v, hc' v⟩, fun v σ => ?_⟩
  apply AlgEquiv.ext
  intro y
  apply Subtype.ext
  apply (ι v).injective
  have h1 := GroundTheory.ProfCoh.gsFinFamily_apply (S : Set (HeightOneSpectrum (𝓞 K)))
    (fun w => ι ⟨w.1, Finset.mem_coe.1 w.2⟩) ⟨v.1, Finset.mem_coe.2 v.2⟩ σ y
  have h2 := he ((ev v σ : Dec (F := K) (Av v)) : G K (AlgebraicClosure ℚ)) y
  refine Eq.trans ?_ h1.symm
  change ι v ((e (toGS (AlgebraicClosure ℚ) _
    ((ev v σ : Dec (F := K) (Av v)) : G K (AlgebraicClosure ℚ))) y :
      GroundTheory.ProfCoh.maxUnramifiedOutside K (AlgebraicClosure ℚ) (S : Set (HeightOneSpectrum (𝓞 K)))) :
        AlgebraicClosure ℚ) = _
  rw [h2, hι]

end PositivityTheory.Lit1.PTN
end
end

